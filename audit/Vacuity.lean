/-!
# Auditoria de vacuidade — `MCore.Material.YMClosure`

A estrutura abaixo é cópia verbatim de `imports/lean/MCore/Material/Closure.lean` (o original
importa `MCore`, mas a estrutura não usa nada de lá; aqui só o Lean core).

Resultado certificado pelo kernel: `MaterialYMProducer` é habitável **sem nenhuma matemática de
Yang–Mills**. Os campos `spectralGap`, `surjectivePhysical`, `continuumControl` são proposições
ESCOLHIDAS por quem constrói a estrutura; basta escolher `True`. Logo um habitante dessa estrutura
não é, por si só, evidência de lacuna de massa. Estado: **CONDICIONAL** (ver `CONDICIONAL.md`).
-/

namespace Audit.YM

structure YMClosure (Regulated Physical : Type) where
  toPhysical : Regulated → Physical
  spectralGap : Prop
  surjectivePhysical : Prop
  continuumControl : Prop
  spectralGap_proof : spectralGap
  surjectivePhysical_proof : surjectivePhysical
  continuumControl_proof : continuumControl

def MaterialYMProducer (Regulated Physical : Type) : Prop :=
  Nonempty (YMClosure Regulated Physical)

/-- Vacuidade 1: para QUALQUER tipo físico habitado o "produtor" existe, com `True` nos três
campos proposicionais. -/
theorem producer_of_inhabited (Regulated Physical : Type) (p : Physical) :
    MaterialYMProducer Regulated Physical :=
  ⟨{ toPhysical := fun _ => p
     spectralGap := True
     surjectivePhysical := True
     continuumControl := True
     spectralGap_proof := trivial
     surjectivePhysical_proof := trivial
     continuumControl_proof := trivial }⟩

/-- Vacuidade 2: mesmo com o tipo físico vazio, basta o regulado ser vazio. -/
theorem producer_of_empty (Physical : Type) : MaterialYMProducer Empty Physical :=
  ⟨{ toPhysical := Empty.elim
     spectralGap := True
     surjectivePhysical := True
     continuumControl := True
     spectralGap_proof := trivial
     surjectivePhysical_proof := trivial
     continuumControl_proof := trivial }⟩

/-- Correção proposta: as três proposições passam a ser PARÂMETROS fixados de fora (e, para valer
como Yang–Mills, iguais aos enunciados de Jaffe–Witten — hoje não enunciáveis na Mathlib). Com
parâmetros, o produtor é exatamente a conjunção deles: nada é escolhido por dentro. -/
structure YMClosureFixed (Regulated Physical : Type) (SpectralGap Surjective Continuum : Prop) where
  toPhysical : Regulated → Physical
  spectralGap_proof : SpectralGap
  surjectivePhysical_proof : Surjective
  continuumControl_proof : Continuum

theorem fixed_iff (Regulated Physical : Type) (p : Physical) (G S C : Prop) :
    Nonempty (YMClosureFixed Regulated Physical G S C) ↔ (G ∧ S ∧ C) :=
  ⟨fun ⟨h⟩ => ⟨h.spectralGap_proof, h.surjectivePhysical_proof, h.continuumControl_proof⟩,
   fun ⟨g, s, c⟩ => ⟨⟨fun _ => p, g, s, c⟩⟩⟩

/-- Com a correção, o mesmo truque NÃO funciona: se a lacuna fixada é `False`, não há produtor. -/
theorem fixed_not_vacuous (Regulated Physical : Type) (S C : Prop) :
    ¬ Nonempty (YMClosureFixed Regulated Physical False S C) :=
  fun ⟨h⟩ => h.spectralGap_proof

/-! ## Linha de explosão (formato NS: testemunha / refutação / dicotomia)

A explosão de Yang–Mills é a AUSÊNCIA de lacuna de massa: espectro de energia acumulando em `0`
acima do vácuo. Com a correção `YMClosureFixed` (proposições fixadas de fora), o formato é exato:
uma testemunha de "sem lacuna" impede o produtor. Para valer sobre o problema, `SpectralGap`
tem de ser o enunciado de Jaffe–Witten (não enunciável na Mathlib v4.34.1). -/

/-- Testemunha de explosão: a negação da lacuna fixada. -/
def GaplessWitness (SpectralGap : Prop) : Prop := ¬ SpectralGap

theorem explosion_refutes (Regulated Physical : Type) {G S C : Prop} (w : GaplessWitness G) :
    ¬ Nonempty (YMClosureFixed Regulated Physical G S C) :=
  fun ⟨h⟩ => w h.spectralGap_proof

/-- Dicotomia (com tipo físico habitado e `S`, `C` dados): produtor ⇔ não há explosão. -/
theorem producer_iff_no_explosion (Regulated Physical : Type) (p : Physical) {G S C : Prop}
    (hS : S) (hC : C) :
    Nonempty (YMClosureFixed Regulated Physical G S C) ↔ ¬ GaplessWitness G := by
  rw [fixed_iff Regulated Physical p]
  constructor
  · intro h w
    exact w h.1
  · intro h
    exact ⟨Classical.byContradiction h, hS, hC⟩

end Audit.YM

#print axioms Audit.YM.producer_of_inhabited
#print axioms Audit.YM.producer_of_empty
#print axioms Audit.YM.fixed_iff
#print axioms Audit.YM.fixed_not_vacuous
#print axioms Audit.YM.explosion_refutes
#print axioms Audit.YM.producer_iff_no_explosion
