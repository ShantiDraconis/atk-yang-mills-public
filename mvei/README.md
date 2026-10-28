# MVEI kernel check — m-core-yang-mills

This folder records what the Lean 4 kernel said about the Lean sources of the private repository `ShantiDraconis/m-core-yang-mills`. The sources are published in [`imports/m-core-yang-mills/`](../imports/m-core-yang-mills/).

## What is published

* Source: `ShantiDraconis/m-core-yang-mills`, commit `1c324b533e85bf79cf5b55298fa9f42af4e8f30f` (2026-10-11T23:07:44Z).
* 24 files: 19 `.lean` files and the Lake files (`lakefile.*`, `lean-toolchain`, `lake-manifest.json`). Paths are the same as in the source repository.
* Nothing else from the private repository is published (documents, commercial license, prompts, storefront material).
* `SOURCES.sha256` lists every published file with its SHA-256. From the repository root: `sha256sum -c mvei/SOURCES.sha256`.

## What the kernel said

MVEI verification of 2026-10-28T13:47:17+00:00, on commit `1c324b533e85bf79cf5b55298fa9f42af4e8f30f`. Each theorem was read with `Lean.collectAxioms`, the function behind `#print axioms`.

| Lean project | Lean version | Build | Closed | Conditional | Open (`sorry`) |
|---|---|---|---:|---:|---:|
| `.` | v4.19.0 | OK | 85 | 0 | 0 |
| `atk-kernel` | v4.34.1 | OK | 2 | 0 | 0 |

| Closed theorems in this repository | |
|---|---:|
| Counting each project | 87 |
| Unique (name + statement) | 87 |
| Unique, without the lemmas Lean generates itself (`eq_1`, `mk.inj`, `sizeOf_spec`, `deriving`) | 25 |

*Closed* means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`. It says that the statement as written in the file is proved; it does not say that an open problem is solved. Every statement is in `VERIFICACAO.json`. *Conditional* means the proof also uses axioms declared in the repository; *open* means it uses `sorry`.

### Declared theorems

The `.lean` files of the verified commit declare 25 `theorem`/`lemma` (counting copies). The kernel checked 21 of them (21 closed, 0 conditional, 0 open). The closed count in the table above is larger: it also counts the theorems Lean generates by itself (equation lemmas, structure fields, `deriving`), which are not written in the text. 4 were not reached by any build:

| Reason | Theorems |
|---|---:|
| the project built, but the file is not part of the lakefile target | 4 |

A file-by-file check of these (each file through Lean, with `#print axioms` for each theorem) is running in the MVEI pipeline; this folder will be updated with the result.

## Files in this folder

* `VERIFICACAO.json` — each Lean project of this repository, each theorem the kernel read, its statement, its axioms and its state (`fechado` closed, `condicional` conditional, `aberto-sorry` open)
* `TEOREMAS.csv` — each declared `theorem`/`lemma`: file, line, state in the kernel (`nao_checado` = not checked) and, if not checked, why (in Portuguese)
* `BUILD_LOG.txt` — one block per project: Lean version, result, errors
* `SOURCE.json` — source commit, verified commit and dates, machine-readable
* `SOURCES.sha256` — SHA-256 of every published file

## Reproduce

```
cd imports/m-core-yang-mills/<project>   # a project folder from the table above ('.' is imports/m-core-yang-mills)
lake exe cache get           # only for projects that require Mathlib
lake build
```

Each project uses the Lean version in its own `lean-toolchain`, which elan installs. The MVEI pipeline that produced these results is in the author's repository and is not public.
