import MCore.YangMills.A1.RegulatedConstruction

namespace MCore.YangMills.A1

open Filter Topology

def trivialLimitCoordinates (C : RegulatedYM4Construction) :
    A1LimitCoordinates C where
  cutoffValue := fun _ => 0
  volumeValue := fun _ => 0

def trivialUniformRegulatorControl (C : RegulatedYM4Construction) :
    UniformRegulatorControl C where
  coordinates := trivialLimitCoordinates C
  estimate := fun _ _ => 0
  nonnegative := fun _ _ => le_rfl
  cutoffLimit := fun _ => tendsto_const_nhds
  volumeLimit := fun _ => tendsto_const_nhds
  jointLimit := tendsto_const_nhds

theorem uniform_regulator_control_inhabited_for_every_construction
    (C : RegulatedYM4Construction) :
    Nonempty (UniformRegulatorControl C) :=
  ⟨trivialUniformRegulatorControl C⟩

theorem a1_uniformity_bridge_inhabited_for_every_construction
    (C : RegulatedYM4Construction) :
    A1UniformityBridge C :=
  uniform_regulator_control_inhabited_for_every_construction C

theorem pointwise_to_uniform_bridge_vacuously_holds
    (C : RegulatedYM4Construction) :
    PointwiseToUniformBridge C := by
  intro _
  exact a1_uniformity_bridge_inhabited_for_every_construction C

end MCore.YangMills.A1
