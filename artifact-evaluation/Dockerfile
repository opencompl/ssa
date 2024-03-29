# First image to generate Alive test cases
FROM python:2.7 as alivePy
RUN apt-get update -y \
 && DEBIAN_FRONTEND="noninteractive" apt-get install --yes git
RUN pip install stopit z3-solver==4.8.17
RUN mkdir -p /code/ssa/SSA/Projects/InstCombine
RUN git clone https://github.com/opencompl/alive /code/ssa/related-work/alive/alive \
 && cd /code/ssa/related-work/alive/alive \
 && git checkout c4c0

WORKDIR /code/ssa/related-work/alive/alive
RUN python ./1-tolean.py



# Main Lean image
FROM ubuntu:24.04
WORKDIR /code

# Install dependencies
RUN apt-get update -y \
    && DEBIAN_FRONTEND="noninteractive" apt-get install --yes \
        tzdata \
        build-essential \
        cmake \
        git \
        ninja-build \
        gdb curl wget

# Install Lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf > /code/elan.sh \
    && sh /code/elan.sh -y # elan
ENV PATH /root/.elan/bin:$PATH
ENV LIBRARY_PATH /root/.elan/lib:$LIBRARY_PATH

# Download & build lean-mlir
RUN curl -L https://github.com/opencompl/ssa/archive/refs/tags/v0.1.0.tar.gz > /code/ssa.tar.gz # SSA tar file
RUN tar xf ssa.tar.gz && ls /code/ && mv ssa-0.1.0 ssa # untar
WORKDIR /code/ssa
RUN lake -R exe cache get
RUN lake build SSA mlirnatural

# Copy & build Alive examples
COPY --from=0 /code/ssa/SSA/Projects/InstCombine/AliveAutoGenerated.lean /code/ssa/SSA/Projects/InstCombine/AliveAutoGenerated.lean
RUN lake build AliveExamples

USER root
