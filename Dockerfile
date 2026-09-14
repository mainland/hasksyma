ARG GHC_VERSION=9.12.4

FROM haskell:${GHC_VERSION}

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    libzmq3-dev \
    pkg-config \
    python3-pip \
    python3-venv \
    sudo \
  && rm -rf /var/lib/apt/lists/*

ARG USERNAME=haskell
ARG USER_UID=1000
ARG USER_GID=${USER_UID}

RUN groupadd --gid "${USER_GID}" "${USERNAME}" \
  && useradd --uid "${USER_UID}" --gid "${USER_GID}" --create-home "${USERNAME}" \
  && echo "${USERNAME} ALL=(root) NOPASSWD:ALL" > "/etc/sudoers.d/${USERNAME}" \
  && chmod 0440 "/etc/sudoers.d/${USERNAME}" \
  && mkdir /venv /workspace \
  && chown "${USER_UID}:${USER_GID}" /venv /workspace

USER ${USERNAME}

ENV VIRTUAL_ENV=/venv
ENV PATH="/venv/bin:/home/${USERNAME}/.local/bin:${PATH}"

RUN python3 -m venv "${VIRTUAL_ENV}" \
  && pip install --no-cache-dir jupyterlab \
  && cabal update \
  && cabal install ihaskell-0.13.0.0 \
    --install-method=copy \
    --overwrite-policy=always

WORKDIR /workspace

RUN ihaskell install

EXPOSE 8888

CMD ["jupyter", "lab", "--ip=0.0.0.0", "--no-browser"]
