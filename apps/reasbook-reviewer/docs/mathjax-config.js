window.MathJax = {
  tex: {
    inlineMath: [["\\(", "\\)"], ["$", "$"]],
    displayMath: [["\\[", "\\]"], ["$$", "$$"]],
    processEnvironments: true,
    processEscapes: true,
    tags: "ams"
  },
  chtml: {
    displayOverflow: "linebreak",
    linebreaks: { inline: true, width: "container" }
  },
  options: { skipHtmlTags: ["script", "noscript", "style", "textarea", "pre", "code"] },
  startup: {
    typeset: false,
    ready() {
      MathJax.startup.defaultReady();
      window.dispatchEvent(new Event("mathjax-ready"));
    }
  }
};
