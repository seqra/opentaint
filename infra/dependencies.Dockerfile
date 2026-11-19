FROM ubuntu:24.04

RUN apt-get update && apt-get install -y -q --no-install-recommends ca-certificates curl wget apt-transport-https gpg unzip language-pack-en \
    && update-locale LANG=en_US.UTF-8
ENV LC_ALL=en_US.UTF-8

# Java 8, 11, 17, 21, latest (25)
RUN wget -qO - https://packages.adoptium.net/artifactory/api/gpg/key/public | gpg --dearmor | tee /etc/apt/trusted.gpg.d/adoptium.gpg > /dev/null \
    && echo "deb https://packages.adoptium.net/artifactory/deb $(awk -F= '/^VERSION_CODENAME/{print$2}' /etc/os-release) main" | tee /etc/apt/sources.list.d/adoptium.list \
    && apt update \
    && apt install -y -q --no-install-recommends temurin-8-jdk  && mv /usr/lib/jvm/temurin-8-jdk* /usr/lib/jvm/8-jdk \
    && apt install -y -q --no-install-recommends temurin-11-jdk && mv /usr/lib/jvm/temurin-11-jdk* /usr/lib/jvm/11-jdk \
    && apt install -y -q --no-install-recommends temurin-17-jdk && mv /usr/lib/jvm/temurin-17-jdk* /usr/lib/jvm/17-jdk \
    && apt install -y -q --no-install-recommends temurin-21-jdk && mv /usr/lib/jvm/temurin-21-jdk* /usr/lib/jvm/21-jdk \
    && apt install -y -q --no-install-recommends temurin-25-jdk && mv /usr/lib/jvm/temurin-25-jdk* /usr/lib/jvm/25-jdk \
    && rm /usr/bin/java && ln -s /usr/lib/jvm/17-jdk/bin/java /usr/bin/java \
    && rm -rf /var/lib/apt/lists/*

# Gradle
ENV GRADLE_VERSION=gradle-8.10
RUN wget --no-verbose https://services.gradle.org/distributions/${GRADLE_VERSION}-bin.zip -O /tmp/${GRADLE_VERSION}-bin.zip \
    && unzip -q -d /opt/gradle /tmp/${GRADLE_VERSION}-bin.zip \
    && rm /tmp/${GRADLE_VERSION}-bin.zip
ENV PATH="/opt/gradle/${GRADLE_VERSION}/bin:${PATH}"

# Maven
ENV MAVEN_VERSION=3.9.14
RUN wget --no-verbose "https://www.apache.org/dyn/closer.lua/maven/maven-3/${MAVEN_VERSION}/binaries/apache-maven-${MAVEN_VERSION}-bin.tar.gz?action=download" -O /tmp/${MAVEN_VERSION}-bin.tar.gz \
    && mkdir /opt/maven && tar xzvf /tmp/${MAVEN_VERSION}-bin.tar.gz -C /opt/maven \
    && rm /tmp/${MAVEN_VERSION}-bin.tar.gz
ENV PATH="/opt/maven/apache-maven-${MAVEN_VERSION}/bin:${PATH}"

# Fix maven repository setting
RUN apt-get update && apt-get install -y -q --no-install-recommends \
                git inetutils-tools \
                && rm -rf /var/lib/apt/lists/* \
                && rm /opt/maven/*/conf/settings.xml \
                && ln -s /opt/maven/*/bin/mvn /usr/bin/mvn \
                && ln -s /opt/gradle/*/bin/gradle /usr/bin/gradle

# Go, and a C compiler for cgo
ENV GO_VERSION=1.27.4
RUN apt-get update && apt-get install -y -q --no-install-recommends gcc libc6-dev \
    && rm -rf /var/lib/apt/lists/*
RUN arch="$(dpkg --print-architecture)" \
    && case "$arch" in \
        amd64) sha256=7226736c2339719cda28fbf3a54d71aa63bcefe376e98cef00034268dab24840 ;; \
        arm64) sha256=3392582988a273a87ab5043ee1b2c9c17a2c3c00580bf9326c47a2e0aaaeac92 ;; \
        *) echo "No Go archive for $arch" >&2; exit 1 ;; \
    esac \
    && wget --no-verbose https://go.dev/dl/go${GO_VERSION}.linux-${arch}.tar.gz -O /tmp/go.tar.gz \
    && echo "$sha256  /tmp/go.tar.gz" | sha256sum -c - \
    && tar xzf /tmp/go.tar.gz -C /usr/local \
    && rm /tmp/go.tar.gz \
    && mkdir -m 1777 /go
ENV GOPATH=/go
ENV PATH="/usr/local/go/bin:${PATH}"

ENV JAVA_8_HOME=/usr/lib/jvm/8-jdk
ENV JAVA_11_HOME=/usr/lib/jvm/11-jdk
ENV JAVA_17_HOME=/usr/lib/jvm/17-jdk
ENV JAVA_21_HOME=/usr/lib/jvm/21-jdk
ENV JAVA_LATEST_HOME=/usr/lib/jvm/25-jdk

RUN mkdir -p /usr/local/lib/opentaint/jre/bin \
    && ln -sf /usr/lib/jvm/21-jdk/bin/java /usr/local/lib/opentaint/jre/bin/java
