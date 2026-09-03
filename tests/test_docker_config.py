from __future__ import annotations

from pathlib import Path
import unittest

import yaml


ROOT = Path(__file__).resolve().parents[1]


class DockerConfigTests(unittest.TestCase):
    def test_build_context_contains_site_and_nginx_configuration(self) -> None:
        patterns = (ROOT / ".dockerignore").read_text(encoding="utf-8").splitlines()
        required_includes = (
            "!docker/",
            "!docker/nginx.conf",
            "!ReasBookWeb/",
            "!ReasBookWeb/_site/",
            "!ReasBookWeb/_site/**",
        )
        for pattern in required_includes:
            with self.subTest(pattern=pattern):
                self.assertIn(pattern, patterns)
                self.assertGreater(patterns.index(pattern), patterns.index("*"))

        dockerfile = (ROOT / "Dockerfile").read_text(encoding="utf-8")
        self.assertIn(
            "COPY docker/nginx.conf /etc/nginx/conf.d/default.conf",
            dockerfile,
        )
        self.assertIn(
            "COPY ReasBookWeb/_site/ /usr/share/nginx/html/",
            dockerfile,
        )

    def test_service_maps_the_generated_site_prefix(self) -> None:
        compose = yaml.safe_load(
            (ROOT / "docker-compose.yml").read_text(encoding="utf-8")
        )
        build = compose["services"]["site"]["build"]
        self.assertEqual(build["context"], ".")
        self.assertEqual(build["dockerfile"], "Dockerfile")

        nginx = (ROOT / "docker" / "nginx.conf").read_text(encoding="utf-8")
        self.assertIn("return 308 /ReasBook/;", nginx)
        self.assertIn("location /ReasBook/", nginx)
        self.assertIn("alias /usr/share/nginx/html/;", nginx)


if __name__ == "__main__":
    unittest.main()
