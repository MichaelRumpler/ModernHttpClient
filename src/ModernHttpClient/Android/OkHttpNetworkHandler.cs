using System;
using System.Collections.Generic;
using System.Linq;
using System.Net;
using System.Net.Http;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using System.Security.Cryptography.X509Certificates;

using Java.Interop;
using Javax.Net.Ssl;
using Java.Security;
using Java.Security.Cert;

using Square.OkHttp3;

namespace ModernHttpClient
{
	public class NativeMessageHandler : HttpClientHandler
    {
        readonly OkHttpClient client;
        readonly CacheControl noCacheCacheControl = default(CacheControl);
        readonly bool throwOnCaptiveNetwork;

        readonly Dictionary<HttpRequestMessage, WeakReference> registeredProgressCallbacks =
            new Dictionary<HttpRequestMessage, WeakReference>();
        readonly Dictionary<string, string> headerSeparators = 
            new Dictionary<string,string>(){ 
                {"User-Agent", " "}
            };

        public bool DisableCaching { get; set; }

        public NativeMessageHandler() : this(false, false) {}

        public NativeMessageHandler(bool throwOnCaptiveNetwork, bool customSSLVerification, NativeCookieHandler cookieHandler = null)
        {
            this.throwOnCaptiveNetwork = throwOnCaptiveNetwork;

			if (customSSLVerification)
			{
				var tm = new CustomX509TrustManager();
				var sslCtx = SSLContext.GetInstance("TLSv1.2");
				sslCtx.Init(null, new ITrustManager[] { tm }, null);

				client = new OkHttpClient.Builder()
					.HostnameVerifier(new HostnameVerifier())
					.SslSocketFactory(sslCtx.SocketFactory, tm)
					.Build();
			}
			else
				client = new OkHttpClient();


			noCacheCacheControl = (new CacheControl.Builder()).NoCache().Build();
        }

		public void RegisterForProgress(HttpRequestMessage request, ProgressDelegate callback)
        {
            if (callback == null && registeredProgressCallbacks.ContainsKey(request)) {
                registeredProgressCallbacks.Remove(request);
                return;
            }

            registeredProgressCallbacks[request] = new WeakReference(callback);
        }

        ProgressDelegate getAndRemoveCallbackFromRegister(HttpRequestMessage request)
        {
            ProgressDelegate emptyDelegate = delegate { };

            lock (registeredProgressCallbacks) {
                if (!registeredProgressCallbacks.ContainsKey(request)) return emptyDelegate;

                var weakRef = registeredProgressCallbacks[request];
                if (weakRef == null) return emptyDelegate;

                var callback = weakRef.Target as ProgressDelegate;
                if (callback == null) return emptyDelegate;

                registeredProgressCallbacks.Remove(request);
                return callback;
            }
        }

        string getHeaderSeparator(string name)
        {
            if (headerSeparators.ContainsKey(name)) {
                return headerSeparators[name];
            }

            return ",";
        }

		protected override async Task<HttpResponseMessage> SendAsync(HttpRequestMessage request, CancellationToken cancellationToken)
        {
            var java_uri = request.RequestUri.GetComponents(UriComponents.AbsoluteUri, UriFormat.UriEscaped);
            var url = new Java.Net.URL(java_uri);

            var body = default(RequestBody);
            if (request.Content != null) {
                var bytes = await request.Content.ReadAsByteArrayAsync().ConfigureAwait(false);

                var contentType = "text/plain";
                if (request.Content.Headers.ContentType != null) {
                    contentType = String.Join(" ", request.Content.Headers.GetValues("Content-Type"));
                }
                body = RequestBody.Create(MediaType.Parse(contentType), bytes);
            }

            var builder = new Request.Builder()
                .Method(request.Method.Method.ToUpperInvariant(), body)
                .Url(url);

            if (DisableCaching) {
                builder.CacheControl(noCacheCacheControl);
            }

            var keyValuePairs = request.Headers
                .Union(request.Content != null ?
                    (IEnumerable<KeyValuePair<string, IEnumerable<string>>>)request.Content.Headers :
                    Enumerable.Empty<KeyValuePair<string, IEnumerable<string>>>());

            foreach (var kvp in keyValuePairs)
				builder.AddHeader(kvp.Key, String.Join(getHeaderSeparator(kvp.Key), kvp.Value));

            cancellationToken.ThrowIfCancellationRequested();

            var rq = builder.Build();
            var call = client.NewCall(rq);

            // NB: Even closing a socket must be done off the UI thread. Cray!
            cancellationToken.Register(() => Task.Run(() => call.Cancel()));

			var resp = await call.ExecuteAsync().ConfigureAwait(false);

			var newReq = resp.Request();
            var newUri = newReq == null ? null : newReq.Url();
            request.RequestUri = new Uri(newUri.ToString());
            if (throwOnCaptiveNetwork
				&& newUri != null
				&& url.Host != newUri.Host())
                    throw new CaptiveNetworkException(new Uri(java_uri), new Uri(newUri.ToString()));

            var respBody = resp.Body();

            cancellationToken.ThrowIfCancellationRequested();

            var ret = new HttpResponseMessage((HttpStatusCode)resp.Code());
            ret.RequestMessage = request;
            ret.ReasonPhrase = resp.Message();
            if (respBody != null) {
                var content = new ProgressStreamContent(respBody.ByteStream(), CancellationToken.None);
                content.Progress = getAndRemoveCallbackFromRegister(request);
                ret.Content = content;
            } else {
                ret.Content = new ByteArrayContent(new byte[0]);
            }

            var respHeaders = resp.Headers();
            foreach (var k in respHeaders.Names()) {
                ret.Headers.TryAddWithoutValidation(k, respHeaders.Get(k));
                ret.Content.Headers.TryAddWithoutValidation(k, respHeaders.Get(k));
            }

            return ret;
        }
    }

	internal class HostnameVerifier : Java.Lang.Object, IHostnameVerifier
	{
		static readonly Regex cnRegex = new Regex(@"CN\s*=\s*([^,]*)", RegexOptions.Compiled | RegexOptions.CultureInvariant | RegexOptions.Singleline);

		public bool Verify(string hostname, ISSLSession session)
		{
			if (ServicePointManager.ServerCertificateValidationCallback == null)
				return HttpsURLConnection.DefaultHostnameVerifier.Verify(hostname, session);

			var certificates = session.GetPeerCertificates();
			return Verify(certificates, hostname);
		}

		public static bool Verify(Certificate[] certificates, string hostname = null)
		{
			var chain = new X509Chain();
			X509Certificate2 root = null;
			var errors = System.Net.Security.SslPolicyErrors.None;

			// Build certificate chain and check for errors
			if (certificates == null || certificates.Length == 0)
			{//no cert at all
				errors = System.Net.Security.SslPolicyErrors.RemoteCertificateNotAvailable;
				goto bail;
			}

			var netCerts = certificates.Select(x => new X509Certificate2(x.GetEncoded())).ToArray();

			for (int i = 1; i < netCerts.Length; i++)
				chain.ChainPolicy.ExtraStore.Add(netCerts[i]);

			root = netCerts[0];

			chain.ChainPolicy.RevocationFlag = X509RevocationFlag.EntireChain;
			chain.ChainPolicy.RevocationMode = X509RevocationMode.NoCheck;
			chain.ChainPolicy.UrlRetrievalTimeout = new TimeSpan(0, 1, 0);
			chain.ChainPolicy.VerificationFlags = X509VerificationFlags.AllowUnknownCertificateAuthority;

			if (!chain.Build(root))
			{
				errors = System.Net.Security.SslPolicyErrors.RemoteCertificateChainErrors;
				goto bail;
			}

			var subject = root.Subject;
			var subjectCn = cnRegex.Match(subject).Groups[1].Value;
			if (hostname != null)
			{
				if (String.IsNullOrWhiteSpace(subjectCn) || !Utility.MatchHostnameToPattern(hostname, subjectCn))
				{
					errors = System.Net.Security.SslPolicyErrors.RemoteCertificateNameMismatch;
					goto bail;
				}
			}
			else
			{
				// I don't have the hostname here, so I can't verify it.
				// but I can read it from the certificate and use as sender
				hostname = subjectCn;
			}

			bail:
			// Call the delegate to validate
			return ServicePointManager.ServerCertificateValidationCallback(hostname, root, chain, errors);
		}
	}

	internal class CustomX509TrustManager : Java.Lang.Object, IX509TrustManager
    {
		private IX509TrustManager defaultTrustManager;
		private IX509TrustManager DefaultTrustManager
		{
			get
			{
				if(defaultTrustManager == null)
				{
					var algorithm = TrustManagerFactory.DefaultAlgorithm;
					var defaultTrustManagerFactory = TrustManagerFactory.GetInstance(algorithm);
					defaultTrustManagerFactory.Init((KeyStore)null);
					var trustManagers = defaultTrustManagerFactory.GetTrustManagers();
					defaultTrustManager = trustManagers[0].JavaCast<IX509TrustManager>();
				}
				return defaultTrustManager;
			}
		}

        public void CheckClientTrusted(Java.Security.Cert.X509Certificate[] chain, string authType)
        {
            // we are the client
        }

        public void CheckServerTrusted(Java.Security.Cert.X509Certificate[] certificates, string authType)
        {
			if (ServicePointManager.ServerCertificateValidationCallback == null)
			{
				DefaultTrustManager.CheckServerTrusted(certificates, authType);
			}
			else
			{
				var isvalid = HostnameVerifier.Verify(certificates);
				if(!isvalid)
					throw new CertificateException("Server certificate is not trusted.");
			}
        }

        Java.Security.Cert.X509Certificate[] IX509TrustManager.GetAcceptedIssuers()
        {
            return new Java.Security.Cert.X509Certificate[0];
        }
    }
}
