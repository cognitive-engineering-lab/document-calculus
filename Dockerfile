FROM ocaml/opam:ubuntu-22.04-ocaml-4.13

# Copy files over w/ correct permissions
USER root
COPY . /app
RUN chown opam /app
USER opam
WORKDIR /app

# Install dependencies
RUN opam install . --deps-only --locked