module

public import Jsp000881.Counting
import all Jsp000881.Counting
public import Jsp000881.Heights
import all Jsp000881.Heights
public import Mathlib.Data.Int.Interval

public section

namespace Jsp000881

def ParameterBox (θ : PlaneIndex) (z : ℤ) : Prop :=
  z * z ≤ Plane.W * θ.1 ∧ Plane.W * θ.1 ≤ 2 * (z * z) ∧
  z ≤ Plane.W * θ.2.1 ∧ Plane.W * θ.2.1 ≤ 2 * z ∧
  z ≤ Plane.W * θ.2.2 ∧ Plane.W * θ.2.2 ≤ 2 * z

/-- Every prime modulus admits a point where all six affine forms are nonzero. -/
def LocallyAdmissible (θ : PlaneIndex) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ nm : ℤ × ℤ, ∀ i : Fin 6, ¬ (p : ℤ) ∣ (sextupleOn θ nm).coord i

def InRectangle (T : ℤ) (nm : ℤ × ℤ) : Prop :=
  T ≤ -(15 * (508 * nm.1)) ∧ -(15 * (508 * nm.1)) ≤ 2 * T ∧
  0 ≤ 31 * (3918 + 508 * nm.2) ∧ 100000 * (31 * (3918 + 508 * nm.2)) ≤ T

noncomputable def latticeRectangle (T : ℤ) : Finset (ℤ × ℤ) := by
  classical
  let I := Finset.Icc (-2 * T - 3918) (2 * T + 3918)
  exact (I.product I).filter (InRectangle T)

theorem mem_latticeRectangle {T : ℤ} (hT : 0 ≤ T) {nm : ℤ × ℤ} :
    nm ∈ latticeRectangle T ↔ InRectangle T nm := by
  classical
  unfold latticeRectangle
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
      Finset.mem_Icc.mpr ?_⟩, ⟨h1, h2, h3, h4⟩⟩
    · constructor <;> omega
    · constructor <;> omega

noncomputable def primePoints (θ : PlaneIndex) (T : ℤ) : Finset (ℤ × ℤ) := by
  classical
  exact (latticeRectangle T).filter fun nm => ∀ i : Fin 6, ((sextupleOn θ nm).coord i).toNat.Prime

theorem rectangle_heights {θ : PlaneIndex} {z T : ℤ} {nm : ℤ × ℤ}
    (hz : 100 ≤ z) (hT : 3 ≤ T) (hθ : ParameterBox θ z) (hnm : InRectangle T nm) :
    Plane.RectangleHeights (sextupleOn θ nm) z T := by
  obtain ⟨ha, ha', hb, hb', hc, hc'⟩ := hθ
  obtain ⟨hr, hr', hs, hs'⟩ := hnm
  exact Plane.point_rectangle_heights θ.1 θ.2.1 θ.2.2 nm.1 nm.2 z T
    hz hT ha ha' hb hb' hc hc' hr hr' hs hs'

private theorem rectangle_nonnegative {v : Plane.Sextuple} {z T : ℤ}
    (h : Plane.RectangleHeights v z T) : v.CoordinatesNonnegative := by
  have h1 : 127 < v.p1 := h.coordinate_large 0
  have h2 : 127 < v.p2 := h.coordinate_large 1
  have h3 : 127 < v.p3 := h.coordinate_large 2
  have h4 : 127 < v.p4 := h.coordinate_large 3
  have h5 : 127 < v.p5 := h.coordinate_large 4
  have h6 : 127 < v.p6 := h.coordinate_large 5
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem primePoints_realized {θ : PlaneIndex} {z T : ℤ} {nm : ℤ × ℤ} {x : ℝ}
    (hz : 100 ≤ z) (hT : 3 ≤ T) (hθ : ParameterBox θ z) (hnm : nm ∈ primePoints θ T)
    (hx : (3600000000 : ℝ) * (z : ℝ) ^ 3 * (T : ℝ) ^ 2 ≤ x) :
    ComesFrom θ ((sextupleOn θ nm).toPrimes) ∧
      ((sextupleOn θ nm).toPrimes).IsRealizedBelow x := by
  classical
  unfold primePoints at hnm
  obtain ⟨hregion, hprime⟩ := Finset.mem_filter.mp hnm
  have hgeom := rectangle_heights hz hT hθ ((mem_latticeRectangle (by omega)).mp hregion)
  have hnn := rectangle_nonnegative hgeom
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnn
  let v := sextupleOn θ nm
  let s := v.toPrimes
  have hpos1 : (127 : ℤ) < v.p1 := hgeom.coordinate_large 0
  have hpos3 : (127 : ℤ) < v.p3 := hgeom.coordinate_large 2
  have hpos5 : (127 : ℤ) < v.p5 := hgeom.coordinate_large 4
  have hcast1 : (s.p1 : ℤ) = v.p1 := Int.toNat_of_nonneg h1
  have hcast2 : (s.p2 : ℤ) = v.p2 := Int.toNat_of_nonneg h2
  have hcast3 : (s.p3 : ℤ) = v.p3 := Int.toNat_of_nonneg h3
  have hcast4 : (s.p4 : ℤ) = v.p4 := Int.toNat_of_nonneg h4
  have hcast5 : (s.p5 : ℤ) = v.p5 := Int.toNat_of_nonneg h5
  have hcast6 : (s.p6 : ℤ) = v.p6 := Int.toNat_of_nonneg h6
  have horder : s.IsOrderedFresh := by
    refine ⟨hprime 0, hprime 1, hprime 2, hprime 3, hprime 4, hprime 5,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast (show (127 : ℤ) < (s.p1 : ℤ) by simpa only [hcast1] using hpos1)
    · exact_mod_cast (show (127 : ℤ) < (s.p3 : ℤ) by simpa only [hcast3] using hpos3)
    · exact_mod_cast (show (127 : ℤ) < (s.p5 : ℤ) by simpa only [hcast5] using hpos5)
    · exact_mod_cast (show (s.p1 : ℤ) < (s.p2 : ℤ) by simpa only [hcast1, hcast2] using hgeom.first_order)
    · exact_mod_cast (show (s.p3 : ℤ) < (s.p4 : ℤ) by simpa only [hcast3, hcast4] using hgeom.second_order)
    · exact_mod_cast (show (s.p5 : ℤ) < (s.p6 : ℤ) by simpa only [hcast5, hcast6] using hgeom.third_order)
  have hInt : (1828800 : ℤ) * (s.p5 : ℤ) * (s.p6 : ℤ) ≤ 3600000000 * z ^ 3 * T ^ 2 := by
    rw [hcast5, hcast6]
    have h := mul_le_mul_of_nonneg_left hgeom.perimeter_le (by decide : (0 : ℤ) ≤ 3600)
    nlinarith only [h]
  have hReal : (↑(1828800 * s.p5 * s.p6 : ℕ) : ℝ) ≤
      (3600000000 : ℝ) * (z : ℝ) ^ 3 * (T : ℝ) ^ 2 := by exact_mod_cast hInt
  exact ⟨⟨nm, ⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩, horder, hReal.trans hx,
    θ.1, θ.2.1, θ.2.2, nm.1, nm.2, ⟨h1, h2, h3, h4, h5, h6⟩, rfl⟩

noncomputable def primeTuplesOn (θ : PlaneIndex) (T : ℤ) : Finset PrimeTuple :=
  (primePoints θ T).image fun nm => (sextupleOn θ nm).toPrimes

theorem card_primeTuplesOn {θ : PlaneIndex} {z T : ℤ} (hz : 100 ≤ z) (hT : 3 ≤ T)
    (hθ : ParameterBox θ z) : (primeTuplesOn θ T).card = (primePoints θ T).card := by
  classical
  apply Finset.card_image_of_injOn
  intro u hu v hv h
  change u ∈ primePoints θ T at hu
  change v ∈ primePoints θ T at hv
  have hmem {nm : ℤ × ℤ} (hnm : nm ∈ primePoints θ T) : InRectangle T nm := by
    unfold primePoints at hnm
    exact (mem_latticeRectangle (by omega)).mp (Finset.mem_filter.mp hnm).1
  have hu' := rectangle_nonnegative (rectangle_heights hz hT hθ (hmem hu))
  have hv' := rectangle_nonnegative (rectangle_heights hz hT hθ (hmem hv))
  exact Plane.lattice_coordinates_of_eq (toPrimes_inj hu' hv' h)

theorem primeTupleOn_realized {θ : PlaneIndex} {z T : ℤ} {s : PrimeTuple} {x : ℝ}
    (hz : 100 ≤ z) (hT : 3 ≤ T) (hθ : ParameterBox θ z) (hs : s ∈ primeTuplesOn θ T)
    (hx : (3600000000 : ℝ) * (z : ℝ) ^ 3 * (T : ℝ) ^ 2 ≤ x) :
    ComesFrom θ s ∧ s.IsRealizedBelow x := by
  classical
  unfold primeTuplesOn at hs
  obtain ⟨nm, hnm, rfl⟩ := Finset.mem_image.mp hs
  exact primePoints_realized hz hT hθ hnm hx

end Jsp000881
