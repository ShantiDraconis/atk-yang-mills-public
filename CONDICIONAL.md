# Estado: CONDICIONAL — Yang–Mills e lacuna de massa

Auditoria de 13/10/2026 sobre o commit `1962b9c` deste repositório. Mesmo formato em todos os
repositórios públicos ATK. Nada aqui afirma prova nem refutação: **OPEN_MATH = true**.

Legenda: **ABERTO** = alvo exato enunciável, nenhuma declaração desse tipo no kernel ·
**CONDICIONAL** = existe resultado que fecharia o alvo *se* uma hipótese explícita for
demonstrada · **NÃO_ENUNCIÁVEL** = o alvo exato não existe na Mathlib v4.34.1.

## 1. Alvo exato

Enunciado oficial (Jaffe–Witten): para todo grupo de gauge compacto simples `G`, existe uma teoria
quântica de Yang–Mills em `ℝ⁴` satisfazendo axiomas do tipo Wightman/Osterwalder–Schrader, com
lacuna de massa `Δ > 0`.

A Mathlib v4.34.1 não tem teoria quântica de campos axiomática em `ℝ⁴`.
**Estado no portão: NÃO_ENUNCIÁVEL** — nenhuma declaração pode fechar este problema no kernel
hoje; estruturas locais são interfaces.

## 2. Varredura do conteúdo

1 arquivo Lean · 0 `axiom` · 0 `sorry`/`admit`.

## 3. Itens condicionais — o que precisa ser arrumado

| # | Item | Por que é condicional | O que fechar |
|---|---|---|---|
| Y1 | `YMClosure` / `MaterialYMProducer` (`imports/lean/MCore/Material/Closure.lean`) | **Vacuidade certificada pelo kernel** (`audit/Vacuity.lean`): os campos `spectralGap`, `surjectivePhysical`, `continuumControl` são proposições escolhidas por quem constrói a estrutura; com `True` ela é habitada para qualquer tipo físico habitado (`producer_of_inhabited`) e até com regulado vazio (`producer_of_empty`) | Transformar as três proposições em **parâmetros** fixados de fora (`YMClosureFixed`, `fixed_iff`, `fixed_not_vacuous` mostram que assim o truque deixa de funcionar) |
| Y2 | Conteúdo dos parâmetros | Mesmo corrigido, só vale como YM se os parâmetros forem os enunciados de Jaffe–Witten | Formalizar os axiomas OS/Wightman e a lacuna de massa (trabalho de fundação, anterior ao problema) |
| Y3 | `B60ConcretePhysicalAdapter` (alvo registrado em `atk-math-core-public`) | Definição não incluída neste instantâneo; precisa da mesma auditoria de vacuidade | Importar a definição e repetir `audit/Vacuity.lean` para ela |
| Y4 | Compilação | `Closure.lean` importa `MCore`, ausente aqui. (O `audit/Vacuity.lean` compila só com Lean core — workflow `vacuity-check`) | CI a partir do commit de origem (`provenance/`) |

## 3b. Linha de explosão — certificada no kernel (Lean core)

`audit/Vacuity.lean`: `GaplessWitness G := ¬ G` (ausência de lacuna), `explosion_refutes` e
`producer_iff_no_explosion` sobre `YMClosureFixed`. O formato é exato, mas só vale sobre o
problema quando `G` for o enunciado de Jaffe–Witten (não enunciável na Mathlib v4.34.1).

## 3c. Linha de fechamento

Alvo exato **não enunciável** na Mathlib v4.34.1 ⇒ não existe declaração que o portão possa
aceitar ⇒ **CLOSED_MATH = false** necessariamente. A linha passa a funcionar como nos outros
problemas quando a fundação existir (H1/Y2): então o alvo vira um tipo Lean e o mesmo
`closure_gate.py` calcula a bandeira.

## 4. Falsificador exato

Um grupo compacto simples `G` para o qual a teoria quântica em `ℝ⁴` não existe, ou existe com
espectro sem lacuna (`inf spec(H) ∖ {0} = 0`). Não enunciável na Mathlib v4.34.1.

## 5. Condição para mudar o estado

NÃO_ENUNCIÁVEL → ABERTO quando o alvo exato for formalizável (axiomas + lacuna); só então um
fechamento pode ser avaliado pelo portão.

---

**English summary.** Status CONDITIONAL / gate NOT STATABLE (no axiomatic 4D QFT in Mathlib).
Kernel-certified finding: the imported `YMClosure` lets the constructor *choose* its own
propositions, so it is inhabited with `True` for any inhabited physical type — it carries no
Yang–Mills content. Fix: make the propositions external parameters (shown non-vacuous), then bind
them to the Jaffe–Witten statement once it can be formalized.
