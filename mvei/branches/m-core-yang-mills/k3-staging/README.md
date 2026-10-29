# m-core-yang-mills — branch `k3-staging`

Lean sources from the branch `k3-staging` of the private repository `ShantiDraconis/m-core-yang-mills`, commit `7844e7839e38b10c47cf8601eb5e6ce1a3fcb161` (2026-09-15T17:40:45+02:00), that hold theorems found only on branches (no default branch of any repository has a theorem with the same name). Published here: the files with the theorems the kernel closed, the local files they import and the Lake files of their project.

* Branch state: parada (not in the default branch).
* Theorems only on branches, in this branch: 1 — closed 1, conditional 0, open 0, proof error 0, not reached 0, no result 0.
* History: 7 commit(s) of this branch that are not in the default branch, with date and subject, in `certificate.json`.
* `certificate.json` (SHA-256 of its content: `cdd0f62f8296c702de2e8a5531856c75a6e289af337c38a2090520da1930b8cc`) lists every theorem with its state and the axioms beyond the standard three, and the SHA-256 of every published file. From the repository root: `sha256sum -c mvei/branches/m-core-yang-mills/k3-staging/SOURCES.sha256`.

Closed means the kernel accepted the proof and it depends only on `propext`, `Classical.choice` and `Quot.sound`; it proves the statement written in the file and is not a claim that an open problem is solved.

| Theorem | File | State |
|---|---|---|
| `MCore.k3_attack_route_only_holds` | `lean/MCore/AttackDAG/K3AlgebraAttacks.lean`:6 | fechado |
