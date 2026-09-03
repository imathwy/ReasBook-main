from __future__ import annotations

from pathlib import Path
import unittest

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
        self.assertFalse(any("ReasBookWeb" in pattern for pattern in patterns))
                self.assertGreater(patterns.index(pattern), patterns.index("*"))

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


if __name__ == "__main__":
    unittest.main()
