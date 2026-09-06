FROM python:3.11-slim
ENV PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1
WORKDIR /opt/reasbook
COPY apps/reasbook-reviewer/requirements.txt /tmp/reviewer-requirements.txt
RUN python -m pip install --no-cache-dir -r /tmp/reviewer-requirements.txt
COPY sdk/ sdk/
COPY config/ config/
COPY ReasBook/ ReasBook/
COPY apps/reasbook-reviewer/ apps/reasbook-reviewer/
WORKDIR /opt/reasbook/apps/reasbook-reviewer
ENV REASBOOK_ROOT=/opt/reasbook REASBOOK_REVIEWER_HOST=0.0.0.0 REASBOOK_REVIEWER_PORT=8876
EXPOSE 8876
HEALTHCHECK --interval=30s --timeout=5s --start-period=30s CMD python -c "import urllib.request; urllib.request.urlopen('http://127.0.0.1:8876/api/health', timeout=4)"
CMD ["bash", "start_server.sh"]
