package org.opentaint.ir.test.python.tier1

import org.junit.jupiter.api.*
import org.junit.jupiter.api.Tag

@Tag("tier1")
class WebAppBenchmarkTest : BenchmarkTestBase() {

    companion object {
        private val WEB_PROJECTS_DIR: String by lazy {
            System.getProperty("WEB_PROJECTS_DIR") ?: error("WEB_PROJECTS_DIR not set")
        }
    }

    @Test @Timeout(600) fun `webapp - saleor (Django e-commerce)`() =
        analyzeDir("saleor", "$WEB_PROJECTS_DIR/saleor/saleor", "$WEB_PROJECTS_DIR/saleor", "3.12", 1121, 2432, 2606)

    @Test @Timeout(600) fun `webapp - netbox (Django network automation)`() =
        analyzeDir("netbox", "$WEB_PROJECTS_DIR/netbox/netbox", "$WEB_PROJECTS_DIR/netbox/netbox", "3.12", 727, 3631, 350)

    @Test @Timeout(600) fun `webapp - wagtail (Django CMS)`() =
        analyzeDir("wagtail", "$WEB_PROJECTS_DIR/wagtail/wagtail", "$WEB_PROJECTS_DIR/wagtail", "3.10", 697, 1296, 576)

    @Test @Timeout(600) fun `webapp - taiga-back (Django project management)`() =
        analyzeDir("taiga-back", "$WEB_PROJECTS_DIR/taiga-back/taiga", "$WEB_PROJECTS_DIR/taiga-back", "3.10", 526, 1054, 730)

    @Test @Timeout(600) fun `webapp - django-oscar (Django e-commerce)`() =
        analyzeDir("django-oscar", "$WEB_PROJECTS_DIR/django-oscar/src", "$WEB_PROJECTS_DIR/django-oscar/src", "3.10", 314, 637, 155)

    @Test @Timeout(600) fun `webapp - django-rest-framework`() =
        analyzeDir("django-rest-framework", "$WEB_PROJECTS_DIR/django-rest-framework/rest_framework", "$WEB_PROJECTS_DIR/django-rest-framework", "3.10", 66, 193, 135)

    @Test @Timeout(600) fun `webapp - healthchecks (Django monitoring)`() =
        analyzeDir("healthchecks", "$WEB_PROJECTS_DIR/healthchecks/hc", "$WEB_PROJECTS_DIR/healthchecks", "3.10", 223, 213, 295)

    @Test @Timeout(600) fun `webapp - zulip (Django chat)`() =
        analyzeDir("zulip", "$WEB_PROJECTS_DIR/zulip/zerver", "$WEB_PROJECTS_DIR/zulip", "3.10", 1397, 1668, 3593)

    @Test @Timeout(600) fun `webapp - label-studio (Django data labeling)`() =
        analyzeDir("label-studio", "$WEB_PROJECTS_DIR/label-studio/label_studio", "$WEB_PROJECTS_DIR/label-studio", "3.10", 257, 533, 482)

    @Test @Timeout(600) fun `webapp - paperless-ngx (Django document management)`() =
        analyzeDir("paperless-ngx", "$WEB_PROJECTS_DIR/paperless-ngx/src", "$WEB_PROJECTS_DIR/paperless-ngx/src", "3.11", 129, 346, 289)

    @Test @Timeout(600) fun `webapp - flagsmith (Django feature flags)`() =
        analyzeDir("flagsmith", "$WEB_PROJECTS_DIR/flagsmith/api", "$WEB_PROJECTS_DIR/flagsmith/api", "3.11", 686, 1018, 565)

    @Test @Timeout(600) fun `webapp - plane (Django project tracker)`() =
        analyzeDir("plane", "$WEB_PROJECTS_DIR/plane/apps", "$WEB_PROJECTS_DIR/plane/apps/api", "3.10", 449, 739, 368)

    @Test @Timeout(1200) fun `webapp - posthog (Django analytics)`() =
        analyzeDir("posthog", "$WEB_PROJECTS_DIR/posthog/posthog", "$WEB_PROJECTS_DIR/posthog", "3.13", 3204, 6006, 7133)

    @Test @Timeout(600) fun `webapp - sentry (Django error tracking)`() =
        analyzeDir("sentry", "$WEB_PROJECTS_DIR/sentry/src", "$WEB_PROJECTS_DIR/sentry/src", "3.13", 4260, 6991, 6631)

    @Test @Timeout(600) fun `webapp - superset (Flask BI platform)`() =
        analyzeDir("superset", "$WEB_PROJECTS_DIR/superset/superset", "$WEB_PROJECTS_DIR/superset", "3.10", 1164, 1746, 1883)

    @Test @Timeout(600) fun `webapp - redash (Flask dashboarding)`() =
        analyzeDir("redash", "$WEB_PROJECTS_DIR/redash/redash", "$WEB_PROJECTS_DIR/redash", "3.13", 167, 247, 409)

    @Test @Timeout(600) fun `webapp - CTFd (Flask CTF platform)`() =
        analyzeDir("CTFd", "$WEB_PROJECTS_DIR/CTFd/CTFd", "$WEB_PROJECTS_DIR/CTFd", "3.10", 172, 283, 350)

    @Test @Timeout(600) fun `webapp - flaskbb (Flask forum)`() =
        analyzeDir("flaskbb", "$WEB_PROJECTS_DIR/flaskbb/flaskbb", "$WEB_PROJECTS_DIR/flaskbb", "3.12", 100, 231, 290)

    @Test @Timeout(600) fun `webapp - lemur (Flask certificate manager)`() =
        analyzeDir("lemur", "$WEB_PROJECTS_DIR/lemur/lemur", "$WEB_PROJECTS_DIR/lemur", "3.10", 247, 257, 756)

    @Test @Timeout(600) fun `webapp - mealie (FastAPI recipe manager)`() =
        analyzeDir("mealie", "$WEB_PROJECTS_DIR/mealie/mealie", "$WEB_PROJECTS_DIR/mealie", "3.12", 404, 630, 373)

    @Test @Timeout(600) fun `webapp - dispatch (FastAPI incident management)`() =
        analyzeDir("dispatch", "$WEB_PROJECTS_DIR/dispatch/src/dispatch", "$WEB_PROJECTS_DIR/dispatch/src", "3.11", 655, 843, 1976)

    @Test @Timeout(600) fun `webapp - polar (FastAPI billing)`() =
        analyzeDir("polar", "$WEB_PROJECTS_DIR/polar/server/polar", "$WEB_PROJECTS_DIR/polar/server", "3.13", 812, 1862, 966)

    @Test @Timeout(600) fun `webapp - full-stack-fastapi-template`() =
        analyzeDir("fastapi-template", "$WEB_PROJECTS_DIR/full-stack-fastapi-template/backend/app", "$WEB_PROJECTS_DIR/full-stack-fastapi-template/backend", "3.10", 26, 22, 62)
}
