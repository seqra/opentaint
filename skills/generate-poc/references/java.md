# generate-poc — Java / JVM

Language reference for building and starting a JVM app to reproduce against, keyed to the body's step.

## Workflow

### 1. Start the app

Build and start the app the way the project expects, then wait until the port is listening:

- Spring Boot from source — `./mvnw spring-boot:run` or `./gradlew bootRun`
- a built artifact — `java -jar target/<app>.jar`
- a containerized app — `docker compose up`

Loopback bind flags (per the body's Constraints):

- Spring — `--server.address=127.0.0.1`
- a container — `docker run -p 127.0.0.1:8080:8080 …`, or a compose override on the port mapping
