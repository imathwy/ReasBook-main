FROM nginx:1.27-alpine

COPY docker/nginx.conf /etc/nginx/conf.d/default.conf
COPY ReasBookWeb/_site/ /usr/share/nginx/html/

RUN test -f /usr/share/nginx/html/index.html

EXPOSE 80

HEALTHCHECK --interval=30s --timeout=3s --retries=3 \
  CMD wget -qO- http://127.0.0.1/ReasBook/index.html >/dev/null || exit 1
