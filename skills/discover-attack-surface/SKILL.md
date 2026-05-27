---
name: discover-attack-surface
description: Map a Java/Kotlin project's attack surface and turn gaps in rule coverage into concrete rule requirements. Use when a project needs its attack surface mapped into rule requirements (requires a built project model)
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Discover Attack Surface

Identify the attack surface of the target project by reading source code and project structure. Convert each security gap into concrete rule requirements, which will be used for creating test project and rule later

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Project root `<project-root>` — the project sources. Default: current directory
- Project model `<model-dir>` — the built model. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where rule files are written. Default: `.opentaint/tracking`

## Workflow

Requires a built project model — without it you can miss entry points the analyzer actually sees

### 1. Find entry points and sinks

Search the sources for attack surface:

- Spring/JAX-RS endpoints: `@RestController`, `@Controller`, `@RequestMapping`, `@GetMapping`/`@PostMapping`/..., `@Path`, `@GET`/`@POST`
- Servlets: classes extending `HttpServlet` (`doGet`, `doPost`)
- Message handlers: `@JmsListener`, `@KafkaListener`, `@RabbitListener`
- Other external input: `main(String[])`, `@Scheduled` methods reading external state

For each, note what external data enters (params, headers, body, payload) and what dangerous operations it can reach (DB query, file I/O, command exec, outbound HTTP, deserialization, templating)

### 2. Map dependencies to vulnerability classes

Read `build.gradle` / `pom.xml` (or the model) and match each library to the classes it enables:

- Web framework (Spring Boot, Micronaut, Quarkus) → shapes the entry points and request-binding sources
- DB / ORM (JDBC, JPA/Hibernate, MyBatis) → SQLi, especially string-built queries or `${}` mapper interpolation
- Template engines (Thymeleaf, FreeMarker, Velocity) → SSTI and reflected XSS
- HTTP clients (OkHttp, Apache HttpClient, RestTemplate, WebClient) → SSRF
- XML parsers (JAXB, DocumentBuilder, SAXParser) → XXE
- Deserializers (Jackson polymorphic typing, native `ObjectInputStream`, XStream) → insecure deserialization
- File / process APIs (`java.nio.file`, `ProcessBuilder`, `Runtime.exec`) → path traversal, command injection

### 3. Decide which rules to write

Check coverage, then turn each real gap into a requirement:

- Read the built-in rules (`opentaint dev rules-path`) and anything already in `.opentaint/rules`. A source→sink pair is a gap only when no existing rule detects it
- Verify the pair is semantically real before recording it: the source is genuinely attacker-controlled (a request param, header, or body is; an app-internal constant or server config is not), and the sink is genuinely dangerous with tainted input (string-concatenated SQL is; a parameterized query is not). A pair that fails this isn't a rule
- For every uncovered, semantically real pair worth detecting, write one rule tracking file at `<tracking-dir>/rules/<name>.yaml` (per Tracking)

Name the rule `<context>-<vuln-class>` in kebab-case — the sink technology or framework plus the class, e.g. `mybatis-sqli`, `thymeleaf-ssti`, `resttemplate-ssrf`. It must be unique and stable: the name is the tracking file name and follows the rule through every later stage

## Output

- One `<tracking-dir>/rules/<name>.yaml` per proposed rule, with `stages.description: done`, `requirements` filled, and `dependencies` (exact Maven GAV from the build files) the test project needs. `requirements` must reproduce the real flow, not paraphrase it:
  - vuln class / CWE
  - source — fully-qualified entry method, tainted input, `file:line`
  - sink — fully-qualified method, dangerous call, `file:line`
  - flow — intermediate hops as fully-qualified method names
  - the real signatures and annotations, so the test can mirror the actual code
- A brief summary to the caller: one line per rule (name, vuln class, source→sink). Don't paste the full analysis back — the tracking files hold the detail

## Tracking

Create one rule file per proposed rule; fill only the discovery-stage fields:

```yaml
name: mybatis-sqli
rule_id: null               # filled later
finding: null               # filled later
requirements: |
  CWE-89 SQL injection via MyBatis ${} interpolation
  source: com.example.web.OrderController#listOrders(String) — @RequestParam("orderBy"), OrderController.java:42
  flow: orderBy -> com.example.service.OrderService#list(String), OrderService.java:31
                -> com.example.mapper.OrderMapper#selectByOrder(String)
  sink: com.example.mapper.OrderSqlProvider#byOrder — ${orderBy} concatenated into ORDER BY, OrderSqlProvider.java:18
dependencies:               # exact GAV the test project needs, from the build files
  - org.mybatis:mybatis:3.5.13
  - org.springframework:spring-webmvc:5.3.30
stages:
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  mirror the @RequestParam binding and the @SelectProvider signature in the test
```

## Engine notes

- Spring projects: the analyzer auto-discovers Spring endpoints, so you don't have to enumerate every controller — focus on which flows are dangerous
- Generic projects: the analyzer treats all public/protected methods of public classes as entry points

## Gotchas

- Propose a rule only for a real gap; if a built-in already covers the source→sink, don't duplicate it
- Requirements drive a test project someone else builds; vague requirements produce a useless test
- A passing test won't catch a semantically wrong source or sink — verify both are real here, when writing requirements, because nothing downstream re-checks it
