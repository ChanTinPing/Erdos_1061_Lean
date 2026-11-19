module

public import Jsp000881.TriangleCutoff
public import Jsp000881.PrimeCharacter

public section

namespace Jsp000881

/-- The two translated cutoffs can use the canonical character of a prime
field, without supplying any Fourier data. -/
theorem prime_triangle_weights_gowers_bound {p : ℕ} [Fact p.Prime]
    (g₁ g₂ : BoundedAffineWeight (ZMod p)) (gs : List (BoundedAffineWeight (ZMod p)))
    (hlen : gs.length = 3) (hdet : g₁.dir.a * g₂.dir.b - g₁.dir.b * g₂.dir.a ≠ 0)
    (d : LinearDirection (ZMod p)) (c : ZMod p) (f : ZMod p → ℂ)
    (h : ∀ g ∈ g₁ :: g₂ :: gs, g.dir.a * d.b - g.dir.b * d.a ≠ 0)
    {E F : Finset (ZMod p)} (hE : E.Nonempty) (hF : F.Nonempty) (s t : ZMod p)
    {G : ℝ} (hG : 0 ≤ G) (hf : gowersCubeMoment 5 f ≤ G ^ 32) :
    ‖meanC (fun x : ZMod p × ZMod p => triangleCutoff E (x.1 - s) * triangleCutoff F (x.2 - t) *
      (f (linearRow d.a d.b x + c) * affineWeightProduct x (g₁ :: g₂ :: gs)))‖ ≤ G := by
  obtain ⟨χ, hzero, hnorm, hadd, hnontrivial⟩ := exists_unit_additive_character p
  exact triangle_weights_gowers_bound χ hzero hnorm hadd hnontrivial
    g₁ g₂ gs hlen hdet d c f h hE hF s t hG hf

end Jsp000881
