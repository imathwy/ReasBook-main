"""Errors raised by theorem dependency graph generation."""

from __future__ import annotations


class TheoremGraphError(RuntimeError):
    """Base class for graph configuration, extraction, and rendering errors."""


class GraphConfigError(TheoremGraphError):
    """The requested repository or graph configuration is invalid."""


class ExtractionError(TheoremGraphError):
    """A declaration environment could not be exported or decoded."""


class GraphRenderError(TheoremGraphError):
    """Graph data or static assets could not be written."""
