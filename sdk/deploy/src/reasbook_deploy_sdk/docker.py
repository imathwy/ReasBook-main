"""Docker/Compose adapter for the repository's static site deployment."""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
import shutil
import time
from urllib.error import URLError
from urllib.request import urlopen

from .errors import DeployConfigError, DeployExecutionError
from .runtime import Runner, run_command


@dataclass(frozen=True)
class DockerDeploymentConfig:
    repo_root: Path
    compose_file: Path
    site_root: Path
    port: int = 3200
    cache_root: Path | None = None
    skip_build: bool = False
    dry_run: bool = False
    health_attempts: int = 20
    health_interval_seconds: float = 1.0

    def resolved(self) -> "DockerDeploymentConfig":
        try:
            port = int(self.port)
            health_attempts = int(self.health_attempts)
            health_interval = float(self.health_interval_seconds)
        except (TypeError, ValueError) as exc:
            raise DeployConfigError("Docker numeric settings are invalid") from exc
        config = DockerDeploymentConfig(
            repo_root=Path(self.repo_root).expanduser().resolve(),
            compose_file=Path(self.compose_file).expanduser().resolve(),
            site_root=Path(self.site_root).expanduser().resolve(),
            port=port,
            cache_root=(Path(self.cache_root).expanduser().resolve() if self.cache_root else None),
            skip_build=bool(self.skip_build),
            dry_run=bool(self.dry_run),
            health_attempts=health_attempts,
            health_interval_seconds=health_interval,
        )
        config.validate()
        return config

    def validate(self) -> None:
        if not 1 <= self.port <= 65535:
            raise DeployConfigError("Docker site port must be between 1 and 65535")
        if self.health_attempts < 1 or self.health_interval_seconds <= 0:
            raise DeployConfigError("Docker health-check settings must be positive")
        for value in (self.repo_root, self.compose_file, self.site_root, self.cache_root):
            if value is not None and any(char in str(value) for char in "\x00\r\n"):
                raise DeployConfigError("Docker deployment path contains a control character")
        if self.cache_root is not None and (
            self.cache_root == self.repo_root
            or self.repo_root in self.cache_root.parents
            or self.cache_root in self.repo_root.parents
        ):
            raise DeployConfigError("Docker build cache must be outside the checkout")
        expected_site_root = (self.repo_root / "ReasBookWeb" / "_site").resolve()
        if self.site_root != expected_site_root:
            raise DeployConfigError(
                "Docker deployment only supports the repository site directory: "
                f"{expected_site_root}"
            )


def deploy_static(config: DockerDeploymentConfig, *, runner: Runner | None = None) -> None:
    """Build, start, and probe the static site container."""

    config = config.resolved()
    build_script = config.repo_root / "scripts" / "build" / "site.sh"
    if config.dry_run:
        action = "reuse the existing site" if config.skip_build else f"run {build_script}"
        print(f"[docker-deploy] would {action} and start Compose on port {config.port}")
        return
    if not config.compose_file.is_file():
        raise DeployConfigError(f"Compose file does not exist: {config.compose_file}")
    if not config.skip_build:
        if not build_script.is_file() or not os.access(build_script, os.X_OK):
            raise DeployConfigError(f"build script is not executable: {build_script}")
        environment = {}
        if config.cache_root is not None:
            environment["REASBOOK_CACHE_ROOT"] = str(config.cache_root)
        run_command((str(build_script),), runner=runner, cwd=config.repo_root, env=environment)
    if not (config.site_root / "index.html").is_file():
        raise DeployConfigError(
            f"missing generated site: {config.site_root / 'index.html'}"
        )
    if runner is None and shutil.which("docker") is None:
        raise DeployExecutionError("docker is not installed")
    run_command(
        (
            "docker",
            "compose",
            "-f",
            str(config.compose_file),
            "up",
            "-d",
            "--build",
            "--remove-orphans",
        ),
        runner=runner,
        cwd=config.repo_root,
        env={"REASBOOK_PORT": str(config.port)},
    )
    url = f"http://127.0.0.1:{config.port}/ReasBook/"
    for _ in range(config.health_attempts):
        try:
            with urlopen(url, timeout=config.health_interval_seconds) as response:
                if 200 <= response.status < 400:
                    print(f"[docker-deploy] healthy at {url}")
                    return
        except (OSError, URLError):
            pass
        time.sleep(config.health_interval_seconds)
    raise DeployExecutionError(f"container started but health check failed: {url}")


__all__ = ["DockerDeploymentConfig", "deploy_static"]
