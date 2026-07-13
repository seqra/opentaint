# create-pass-through-approximation — Java / JVM

## Workflow

### 1. Read the method's source

If an application-internal dropped method sits in the project's own sources under the project root — read it directly. For a library method, prefer the dependency's source jar; when only bytecode is available, the resolved jars sit under `.opentaint/project/dependencies` — locate the class with `unzip -l <jar> | grep <class-as-path>` (dotted class with `.` → `/`) and disassemble it with `javap -c -p -classpath <jar> <fully.qualified.ClassName>`, or decompile it for readable source.

### 2. Write the config

Each file opens with a `language: java` header line above `passThrough:` — without it the loader silently skips the whole file. Below it, a config is one top-level `passThrough` list, one entry per `function` with its `copy` edges. The vocabulary:

Positions (the base of any `from`/`to`)
- `this`, `result`, `arg(0)`, `arg(1)`, …
- `any(<classifier>)` — expands to every argument matching the classifier (a cartesian product across positions, bound consistently), not a single argument. Rare — prefer an explicit `arg(N)`

Access-path modifiers (list form `[<base>, <modifier>]`)
- A list is ALWAYS `[<base>, <modifier>, …]` — element 0 is the base position, every later element is an access-path modifier. It is NEVER a list of destinations. Putting a second base (`result`, `this`, `arg(N)`) after the base crashes config-load with `Unexpected position modifier: <token>`. To send one source to several destinations, write one `copy` edge per destination (e.g. `from: arg(0)` → `to: arg(1)` and a second edge `from: arg(0)` → `to: result`), never `to: [arg(1), result]`.
- `.<DeclaringClass>#<slot>#<fieldType>` — a field or virtual slot; type it `java.lang.Object`. The slot name is arbitrary (a descriptive name, or the conventional `<rule-storage>` for a generic carrier)
- `[*]` — array element (no leading dot). For `java.util` collections this does not carry element taint; route it through the conventional `.java.lang.Iterable#Element#java.lang.Object` slot instead (as the built-in `List`/`Collection` models do)

Function matching
- Simple: `package.Class#method`
- Complex: `{package, class, name}` — for one hard-to-name function, not for matching many at once
- Overloads: add `signature: (<ParamType>, …) <Return>` to target one overload when others propagate differently; omit it to match every overload by name

Overrides
- `overrides: true` (default): applies to the class and all subclasses
- `overrides: false`: exact class only

Conditions (the only keys that load from YAML)
- take a `pos: <position>`: `typeIs`, `constantMatches`, `constantEq`, `tainted`
- take the position directly, no `pos` field: `isConstant`, `isNull` — adding `pos` fails to load
- nest other conditions: `anyOf`, `allOf`, `not`
- `constantGt` / `constantLt` load but crash the analysis when actually evaluated against a constant (their string-typed bound fails an engine type-check) — avoid until fixed

Simplest form — a direct copy from one position to another:

```yaml
language: java
passThrough:
- function: com.foo.Wrapper#wrap
  copy:
  - from: arg(0)
    to: result
```

Identity copy — copy a position to itself with `from: this, to: this` / `from: arg(0), to: arg(0)`.

Virtual slot — when data lives in the object between calls, the writer and reader route through a virtual slot (the `.<DeclaringClass>#<slot>#java.lang.Object` modifier above):
- the slot name is nominal — the engine never resolves it, so it need not be a real field
- type it `java.lang.Object` — a concrete type can fail the read-out type-check and drop the taint
- the writer and reader must name the identical `Class#slot#java.lang.Object` triple, or the taint drops

#### Patterns

Getter / setter pair — the writer stores into the slot and, being a void mutator, also keeps the receiver's own prior taint (copy `this` to itself); the getter reads the same slot back to `result`:
```yaml
language: java
passThrough:
- function: org.springframework.http.HttpEntity#setBody
  copy:
  - from: arg(0)
    to:
    - this
    - .org.springframework.http.HttpEntity#Body#java.lang.Object
  - from: this
    to: this
- function: org.springframework.http.HttpEntity#getBody
  copy:
  - from:
    - this
    - .org.springframework.http.HttpEntity#Body#java.lang.Object
    to: result
```

Several writers sharing one slot — any of them taints the object, the reader pulls it back:
```yaml
language: java
passThrough:
- function: org.apache.tools.ant.types.FileSet#setDir
  copy:
  - from: arg(0)
    to:
    - this
    - .org.apache.tools.ant.types.FileSet#path#java.lang.Object
- function: org.apache.tools.ant.types.FileSet#setFile
  copy:
  - from: arg(0)
    to:
    - this
    - .org.apache.tools.ant.types.FileSet#path#java.lang.Object
```

Cross-type builder — a builder method consumes an argument and returns a different type; carry the taint along both the chained receiver (for further calls on `this`) and the returned object, slot included. Four copies:
```yaml
language: java
passThrough:
- function: org.springframework.ldap.query.LdapQueryBuilder#filter
  copy:
  - from: arg(0)
    to:
    - result
    - .org.springframework.ldap.query.LdapQuery#filter#java.lang.Object
  - from: arg(0)
    to:
    - this
    - .org.springframework.ldap.query.LdapQueryBuilder#filter#java.lang.Object
  - from: this
    to: result
  - from:
    - this
    - .org.springframework.ldap.query.LdapQueryBuilder#filter#java.lang.Object
    to:
    - result
    - .org.springframework.ldap.query.LdapQuery#filter#java.lang.Object
```

Builder terminal — a no-arg `build()` / `toX()` returns a new object carrying what the builder accumulated; no argument is involved, so copy each slot from `this` to the matching slot on `result` (the setters that filled the builder slot are separate rules of their own):
```yaml
language: java
passThrough:
- function: com.google.common.collect.ImmutableMap$Builder#build
  copy:
  - from:
    - this
    - .java.util.Map#MapKey#java.lang.Object
    to:
    - result
    - .java.util.Map#MapKey#java.lang.Object
  - from:
    - this
    - .java.util.Map#MapValue#java.lang.Object
    to:
    - result
    - .java.util.Map#MapValue#java.lang.Object
```

Conditional propagation — gate a rule with a `condition`:
```yaml
language: java
passThrough:
- function: com.example.lib.Parser#parse
  condition:
    typeIs: java.lang.String
    pos: arg(0)
  copy:
  - from: arg(0)
    to:
    - this
    - .com.example.lib.Parser#parsed#java.lang.Object
```

Overloaded method — `function` matches every overload by name; when two overloads propagate differently, add `signature` (parameter types as FQNs) to target one:
```yaml
language: java
passThrough:
- function: org.springframework.beans.MutablePropertyValues#addPropertyValue
  signature: (org.springframework.beans.PropertyValue) *
  copy:
  - from: arg(0)
    to:
    - this
    - .java.lang.Iterable#Element#java.lang.Object
- function: org.springframework.beans.MutablePropertyValues#addPropertyValue
  signature: (java.lang.String, java.lang.Object) *
  copy:
  - from: arg(1)
    to:
    - this
    - .java.lang.Iterable#Element#java.lang.Object
    - .org.springframework.beans.PropertyValue#Value#java.lang.Object
  - from: arg(0)
    to:
    - this
    - .java.lang.Iterable#Element#java.lang.Object
    - .org.springframework.beans.PropertyValue#Key#java.lang.Object
```

### 3. Common mistakes to check

- the `function` matcher doesn't match the real method — check the package, class, name, and `overrides`
- a `from`/`to` points at the wrong position — it must land where the data actually is
- a broken slot channel — the writer and reader name different `Class#slot#java.lang.Object` triples, or the slot isn't typed `java.lang.Object`, so the taint drops between them
- a config that fails to load — an unknown `condition` key, a bad position, or a 2-part field modifier
- a function without defined `this` argument behavior (copy it on itself if it does not move taint anywhere)
- an interface-keyed model that never fires — when the receiver's concrete collection type is statically known (`new ArrayList<>()`), resolution binds to the concrete override, not the interface, so model the concrete classes the flow actually uses, not only the interface

## Output

Whole-file form — every function in one top-level `passThrough` list:
```yaml
language: java
passThrough:
- function: org.springframework.beans.MutablePropertyValues#add
  copy:
  - from: arg(1)
    to:
    - this
    - .org.springframework.beans.PropertyValue#Value#java.lang.Object
- function: org.springframework.beans.PropertyValue#getValue
  overrides: false
  copy:
  - from:
    - this
    - .org.springframework.beans.PropertyValue#Value#java.lang.Object
    to: result
- function: org.springframework.beans.PropertyValues#getPropertyValues
  copy:
  - from:
    - this
    - .java.lang.Iterable#Element#java.lang.Object
    to:
    - result
    - '[*]'
```
