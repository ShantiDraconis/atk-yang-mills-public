import MCore
namespace MCore.Material
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
end MCore.Material
