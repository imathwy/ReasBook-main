# Package an already-built ReasBook site.
# Build artifacts first: ./build-web.sh
FROM alpine:3.21

RUN apk add --no-cache busybox-extras

COPY ReasBookWeb/_site /srv/ReasBook
RUN test -f /srv/ReasBook/index.html \
	&& printf '%s\n' '<!doctype html><meta http-equiv="refresh" content="0;url=/ReasBook/">' > /srv/index.html

EXPOSE 80
HEALTHCHECK --interval=30s --timeout=3s --retries=3 \
	CMD wget -qO- http://127.0.0.1/ReasBook/ >/dev/null || exit 1

CMD ["httpd", "-f", "-p", "80", "-h", "/srv"]
