import MCore.Material.Closure
namespace ATK.YM
abbrev Material (R P : Type) : Prop := MCore.Material.MaterialYMProducer R P
theorem producer_of_concrete {R P : Type} (h : MCore.Material.YMClosure R P) : Material R P := ⟨h⟩
end ATK.YM
#print axioms ATK.YM.producer_of_concrete
