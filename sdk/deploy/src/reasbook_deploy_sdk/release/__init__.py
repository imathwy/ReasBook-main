"""Immutable static-site release planning and publication."""

from .models import (
    BranchSpec,
    CanonicalProjects,
    DeploymentProfile,
    GitHubPublishProfile,
    ProjectSpec,
    ReleaseArtifactPolicy,
    RegistryBranch,
    ReleasePolicy,
    ReleaseSpec,
    SourceProject,
    ToolchainRegistry,
)
from .bundle import BundleVerifier, ReleaseBundler
from .artifacts import PagesSiteProjector
from .builder import LocalReleaseBuilder
from .build_plan import ReleaseBuildOptions
from .planner import ReleasePlanner
from .service import StaticReleaseService
from .self_hosted import SelfHostedDeployment, SelfHostedInstaller
from .results import ReleaseArtifactRecord, ReleasePackageResult, ReleaseSetManifest

__all__ = [
    "BranchSpec",
    "BundleVerifier",
    "CanonicalProjects",
    "DeploymentProfile",
    "GitHubPublishProfile",
    "LocalReleaseBuilder",
    "PagesSiteProjector",
    "ProjectSpec",
    "ReleaseArtifactPolicy",
    "ReleaseArtifactRecord",
    "ReleasePackageResult",
    "RegistryBranch",
    "ReleasePolicy",
    "ReleaseBundler",
    "ReleaseBuildOptions",
    "ReleasePlanner",
    "ReleaseSpec",
    "ReleaseSetManifest",
    "SourceProject",
    "ToolchainRegistry",
    "StaticReleaseService",
    "SelfHostedDeployment",
    "SelfHostedInstaller",
]
