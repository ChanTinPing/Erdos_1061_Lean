module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Interval

public section

namespace PrimeUniformity

/-- Rational coordinates with bounded reduced numerators and denominators. -/
@[expose] def BoundedRational (H : ℕ) :=
  {q : ℚ // q.num.natAbs ≤ H ∧ q.den ≤ H}

/-- Encode a height-bounded rational by its reduced numerator and the
predecessor of its positive denominator. -/
def boundedRationalEncode (H : ℕ) (q : BoundedRational H) :
    (↑(Finset.Icc (-(H : ℤ)) (H : ℤ))) × Fin H :=
  ⟨⟨q.val.num, by
    rw [Finset.mem_Icc]
    have h := q.property.1
    omega⟩, ⟨q.val.den - 1, by
      have h := q.property.2
      have hpos := q.val.den_pos
      omega⟩⟩

theorem boundedRationalEncode_injective (H : ℕ) :
    Function.Injective (boundedRationalEncode H) := by
  intro x y h
  have hnum : x.val.num = y.val.num :=
    congrArg (fun t => t.1.val) h
  have hden : x.val.den - 1 = y.val.den - 1 :=
    congrArg (fun t => t.2.val) h
  have hx := x.val.den_pos
  have hy := y.val.den_pos
  have hden' : x.val.den = y.val.den := by omega
  apply Subtype.ext
  rw [← x.val.num_divInt_den, ← y.val.num_divInt_den, hnum, hden']

noncomputable instance boundedRationalFintype (H : ℕ) : Fintype (BoundedRational H) :=
  Fintype.ofInjective (boundedRationalEncode H) (boundedRationalEncode_injective H)

/-- A height cutoff of one already allows the zero coordinate. -/
theorem boundedRational_nonempty {H : ℕ} (hH : 1 ≤ H) : Nonempty (BoundedRational H) :=
  ⟨⟨0, by simpa using hH⟩⟩

theorem card_boundedRational_le (H : ℕ) : Fintype.card (BoundedRational H) ≤ (2 * H + 1) * H := by
  have h := Fintype.card_le_of_injective (boundedRationalEncode H) (boundedRationalEncode_injective H)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Int.card_Icc] at h
  have hsize : ((H : ℤ) + 1 - -(H : ℤ)).toNat = 2 * H + 1 := by omega
  rwa [hsize] at h

/-- A rational coordinate table can label a fixed row or an entire system of
annihilator rows. Its cardinal bound is exponential in the number of entries
and polynomial in their height for fixed table size. -/
theorem card_boundedRationalTable_le {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ℕ) :
    Fintype.card (ι → BoundedRational H) ≤ ((2 * H + 1) * H) ^ Fintype.card ι := by
  rw [Fintype.card_fun]
  exact Nat.pow_le_pow_left (card_boundedRational_le H) _

end PrimeUniformity
