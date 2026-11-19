module

public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace PrimeUniformity

variable {ι G A : Type*} [Group G] [CommGroup A]

/-- Common kernel of the two coordinate components of each product character. -/
def coordinateAnnihilator (η θ : ι → G →* A) : Subgroup G :=
  (⨅ i, (η i).ker) ⊓ (⨅ i, (θ i).ker)

/-- The kernel cut out by the product characters on two copies of the group. -/
def pairAnnihilator (η θ : ι → G →* A) : Subgroup (G × G) :=
  ⨅ i, ((η i).comp (MonoidHom.fst G G) * (θ i).comp (MonoidHom.snd G G)).ker

/-- The two coordinate restrictions embed the recovered common kernel into
the same product kernel. -/
theorem coordinateAnnihilator_eq_comap_pair (η θ : ι → G →* A) :
    coordinateAnnihilator η θ =
      (pairAnnihilator η θ).comap (MonoidHom.inl G G) ⊓
        (pairAnnihilator η θ).comap (MonoidHom.inr G G) := by
  ext x
  simp [coordinateAnnihilator, pairAnnihilator]

/-- The common kernel of the recovered characters inherits the lower step of
the pair kernel, as in the last algebraic step of Leng's Type II argument. -/
theorem coordinateAnnihilator_lowerCentralSeries_eq_bot
    (η θ : ι → G →* A) {s : ℕ} (h : (pairAnnihilator η θ).lowerCentralSeries s = ⊥) :
    (coordinateAnnihilator η θ).lowerCentralSeries s = ⊥ := by
  have hle : (coordinateAnnihilator η θ).map (MonoidHom.inl G G) ≤ pairAnnihilator η θ := by
    rw [Subgroup.map_le_iff_le_comap, coordinateAnnihilator_eq_comap_pair]
    exact inf_le_left
  have hinj : Function.Injective (MonoidHom.inl G G) :=
    fun _ _ heq => congrArg Prod.fst heq
  apply (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp
  rw [Subgroup.map_lowerCentralSeries, eq_bot_iff, ← h]
  exact Subgroup.lowerCentralSeries_mono s hle

end PrimeUniformity
