from __future__ import annotations

import tomllib
import unittest
from pathlib import Path

import yaml


ROOT = Path(__file__).resolve().parents[1]


class DockerConfigTests(unittest.TestCase):
    def test_build_context_contains_nginx_configuration(self) -> None:
        patterns = (ROOT / ".dockerignore").read_text(encoding="utf-8").splitlines()
        required_includes = (
            "!docker/",
            "!docker/nginx.conf",
        )
        for pattern in required_includes:
            with self.subTest(pattern=pattern):
                self.assertIn(pattern, patterns)
                self.assertGreater(patterns.index(pattern), patterns.index("*"))
        self.assertFalse(any("ReasBookWeb" in pattern for pattern in patterns))

        dockerfile = (ROOT / "Dockerfile").read_text(encoding="utf-8")
        self.assertIn(
            "COPY docker/nginx.conf /etc/nginx/conf.d/default.conf",
            dockerfile,
        )
        self.assertNotIn("COPY ReasBookWeb/_site/", dockerfile)

    def test_service_maps_the_generated_site_prefix(self) -> None:
        compose = yaml.safe_load(
            (ROOT / "docker-compose.yml").read_text(encoding="utf-8")
        )
        build = compose["services"]["site"]["build"]
        self.assertEqual(build["context"], ".")
        self.assertEqual(build["dockerfile"], "Dockerfile")
        self.assertIn(
            "${REASBOOK_SITE_DIR:-./ReasBookWeb/_site}:/usr/share/nginx/html/ReasBook:ro",
            compose["services"]["site"]["volumes"],
        )

        nginx = (ROOT / "docker" / "nginx.conf").read_text(encoding="utf-8")
        self.assertIn("return 308 /ReasBook/;", nginx)
        self.assertIn("location /ReasBook/", nginx)
        self.assertIn("try_files $uri $uri/ =404;", nginx)
        self.assertIn('Cache-Control "no-cache"', nginx)

    def test_self_hosted_service_tracks_atomic_current_symlink(self) -> None:
        compose = yaml.safe_load(
            (ROOT / "docker-compose.self-hosted.yml").read_text(encoding="utf-8")
        )
        self.assertEqual(compose["name"], "reasbook-self-hosted")
        service = compose["services"]["site"]
        self.assertNotIn("build", service)
        self.assertEqual(
            service["image"],
            "${REASBOOK_NGINX_IMAGE:-nginx:1.30.4-alpine}",
        )
        self.assertEqual(
            service["ports"],
            [
                "${REASBOOK_BIND_ADDRESS:-127.0.0.1}:"
                "${REASBOOK_SELF_HOST_PORT:-8080}:80"
            ],
        )
        self.assertTrue(service["read_only"])
        self.assertIn("no-new-privileges:true", service["security_opt"])
        self.assertEqual(service["restart"], "unless-stopped")
        self.assertCountEqual(
            service["tmpfs"],
            (
                "/var/cache/nginx:size=16m,mode=0755",
                "/var/run:size=1m,mode=0755",
                "/tmp:size=16m,mode=1777",
            ),
        )
        self.assertEqual(service["logging"]["options"]["max-size"], "10m")
        self.assertEqual(service["logging"]["options"]["max-file"], "3")

        volumes = {item["target"]: item for item in service["volumes"]}
        deployment = volumes["/srv/reasbook"]
        self.assertEqual(
            deployment["source"],
            "${REASBOOK_DEPLOY_ROOT:?set REASBOOK_DEPLOY_ROOT to an absolute path}",
        )
        self.assertTrue(deployment["read_only"])
        self.assertFalse(deployment["bind"]["create_host_path"])
        self.assertNotIn("current", deployment["source"])

        nginx_mount = volumes["/etc/nginx/conf.d/default.conf"]
        self.assertEqual(
            nginx_mount["source"], "./config/deploy/nginx-self-hosted.conf"
        )
        self.assertTrue(nginx_mount["read_only"])
        self.assertFalse(nginx_mount["bind"]["create_host_path"])
        self.assertIn(
            "http://127.0.0.1/ReasBook/release-spec.json",
            " ".join(service["healthcheck"]["test"]),
        )

        nginx = (ROOT / "config" / "deploy" / "nginx-self-hosted.conf").read_text(
            encoding="utf-8"
        )
        self.assertIn("root /srv/reasbook/current/public;", nginx)
        self.assertIn("return 308 /ReasBook/;", nginx)
        self.assertIn("location /ReasBook/", nginx)
        self.assertIn("try_files $uri $uri/ =404;", nginx)
        self.assertIn('Cache-Control "no-cache"', nginx)
        self.assertNotIn("open_file_cache", nginx)
        self.assertNotIn("proxy_pass", nginx)
        self.assertFalse(
            (ROOT / "config" / "deploy" / "nginx-self-hosted.conf.example").exists()
        )

    def test_deploy_package_declares_capability_runtime_dependencies(self) -> None:
        metadata = tomllib.loads(
            (ROOT / "sdk" / "deploy" / "pyproject.toml").read_text(encoding="utf-8")
        )
        dependencies = {
            value.split("==", 1)[0].split(">=", 1)[0]
            for value in metadata["project"]["dependencies"]
        }
        self.assertTrue(
            {
                "reasbook-sdk-common",
                "reasbook-build-sdk",
                "verso-build-sdk",
                "theorem-graph-sdk",
                "comparator-sdk",
            }.issubset(dependencies)
        )

    def test_self_hosted_bootstrap_documentation_avoids_http_chicken_and_egg(
        self,
    ) -> None:
        documentation = (ROOT / "sdk" / "deploy" / "README.md").read_text(
            encoding="utf-8"
        )
        bootstrap = documentation.index(
            "For the containerized production server, install the first release"
        )
        compose = documentation.index(
            "docker compose -f docker-compose.self-hosted.yml up -d --wait",
            bootstrap,
        )
        bootstrap_section = documentation[bootstrap:compose]
        self.assertIn("--release-set release-set.json", bootstrap_section)
        self.assertIn("--filesystem-health-only", bootstrap_section)
        self.assertNotIn("--health-url", bootstrap_section)
        self.assertIn(
            "--health-url http://127.0.0.1:8080/ReasBook/release-spec.json",
            documentation[compose:],
        )


if __name__ == "__main__":
    unittest.main()
