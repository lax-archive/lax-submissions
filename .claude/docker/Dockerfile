FROM node:22-bookworm

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install --yes --no-install-recommends \
        bash-completion \
        build-essential \
        ca-certificates \
        curl \
        gh \
        git \
        git-lfs \
        jq \
        less \
        openssh-client \
        procps \
        python3 \
        ripgrep \
        sudo \
        unzip \
        xz-utils \
        zstd \
    && rm -rf /var/lib/apt/lists/*

# Both checked-in agent configurations launch lean-lsp-mcp through uvx.
RUN curl -LsSf https://astral.sh/uv/install.sh \
        | env UV_INSTALL_DIR=/usr/local/bin UV_NO_MODIFY_PATH=1 sh \
    && uvx --version

# These are deliberately refreshed only when the image is rebuilt. The lax
# setup scripts then provision the archive-pinned Lean and mathlib versions in
# the persistent user home at container startup.
RUN npm install --global \
        @anthropic-ai/claude-code \
        @openai/codex \
        lax-archive \
    && npm cache clean --force \
    && codex --version \
    && claude --version \
    && lax --version

ARG USER_UID=1000
ARG USER_GID=1000

# Match the invoking host user so files written through the bind mount retain
# useful ownership. node:22 already has uid/gid 1000; rename that account when
# it matches, or create an account for a different non-root uid/gid.
RUN set -eux; \
    existing_group="$(getent group "$USER_GID" | cut -d: -f1 || true)"; \
    if [ -z "$existing_group" ]; then \
        groupadd --gid "$USER_GID" dev; \
    elif [ "$existing_group" != dev ]; then \
        groupmod --new-name dev "$existing_group"; \
    fi; \
    existing_user="$(getent passwd "$USER_UID" | cut -d: -f1 || true)"; \
    if [ -z "$existing_user" ]; then \
        useradd --create-home --home-dir /home/dev --shell /bin/bash \
            --uid "$USER_UID" --gid "$USER_GID" dev; \
    else \
        if [ "$existing_user" != dev ]; then usermod --login dev "$existing_user"; fi; \
        usermod --home /home/dev --move-home --shell /bin/bash \
            --gid "$USER_GID" dev; \
    fi; \
    mkdir -p /workspace; \
    chown dev:"$USER_GID" /workspace; \
    printf 'dev ALL=(ALL) NOPASSWD:ALL\n' > /etc/sudoers.d/dev; \
    chmod 0440 /etc/sudoers.d/dev

COPY entrypoint.sh /usr/local/bin/lax-container-entrypoint
RUN chmod 0755 /usr/local/bin/lax-container-entrypoint

ENV HOME=/home/dev \
    PATH=/home/dev/.elan/bin:/home/dev/.local/bin:$PATH \
    LAKE_ARTIFACT_CACHE=false \
    DISABLE_AUTOUPDATER=1 \
    NPM_CONFIG_UPDATE_NOTIFIER=false

USER dev
WORKDIR /workspace
ENTRYPOINT ["lax-container-entrypoint"]
CMD ["codex"]
