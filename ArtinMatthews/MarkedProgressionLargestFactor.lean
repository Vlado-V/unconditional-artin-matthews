module

public import ArtinMatthews.MarkedProgressionDivisorPairs
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Remove one largest factor and retain its original position. The
retained product has fourth power at most the cube of the integer bound. -/

namespace ArtinMatthews
open scoped BigOperators

def markedDivisorMoveLast (i : Fin 4) (t : MarkedDivisorQuadruple) : MarkedDivisorQuadruple :=
  match i.val with
  | 0 => (t.2.1,t.2.2.1,t.2.2.2,t.1)
  | 1 => (t.1,t.2.2.1,t.2.2.2,t.2.1)
  | 2 => (t.1,t.2.1,t.2.2.2,t.2.2.1)
  | _ => t

theorem markedDivisorMoveLast_injective (i : Fin 4) :
    Function.Injective (markedDivisorMoveLast i) := by
  rintro ⟨a,b,c,r⟩ ⟨d,e,f,s⟩ h
  fin_cases i <;> simp [markedDivisorMoveLast] at h ⊢ <;> tauto

theorem markedDivisorMoveLast_product (i : Fin 4) (t : MarkedDivisorQuadruple) :
    markedDivisorQuadrupleProduct (markedDivisorMoveLast i t) = markedDivisorQuadrupleProduct t := by
  rcases t with ⟨a,b,c,r⟩
  fin_cases i <;> simp [markedDivisorMoveLast,markedDivisorQuadrupleProduct] <;> ac_rfl

theorem markedDivisorMoveLast_exists (t : MarkedDivisorQuadruple) :
    ∃ i : Fin 4, let u := markedDivisorMoveLast i t
      u.1 ≤ u.2.2.2 ∧ u.2.1 ≤ u.2.2.2 ∧ u.2.2.1 ≤ u.2.2.2 := by
  rcases t with ⟨a,b,c,r⟩
  by_cases ha : b≤a ∧ c≤a ∧ r≤a
  · exact ⟨0,ha⟩
  by_cases hb : a≤b ∧ c≤b ∧ r≤b
  · exact ⟨1,hb⟩
  by_cases hc : a≤c ∧ b≤c ∧ r≤c
  · exact ⟨2,hc⟩
  refine ⟨3,?_⟩
  change a≤r ∧ b≤r ∧ c≤r
  omega

noncomputable def markedDivisorLargestIndex (t : MarkedDivisorQuadruple) : Fin 4 :=
  Classical.choose (markedDivisorMoveLast_exists t)

theorem markedDivisorLargestIndex_bounds (t : MarkedDivisorQuadruple) :
    let u := markedDivisorMoveLast (markedDivisorLargestIndex t) t
    u.1 ≤ u.2.2.2 ∧ u.2.1 ≤ u.2.2.2 ∧ u.2.2.1 ≤ u.2.2.2 :=
  Classical.choose_spec (markedDivisorMoveLast_exists t)

theorem markedDivisorRetained_pow_le {a b c r X : ℕ}
    (ha : a≤r) (hb : b≤r) (hc : c≤r) (hX : a*b*c*r≤X) :
    (a*b*c)^4 ≤ X^3 := by
  have hD : a*b*c ≤ r^3 := by
    calc
      _ ≤ r*r*r := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
      _ = _ := by ring
  calc
    _ = (a*b*c)^3*(a*b*c) := by ring
    _ ≤ (a*b*c)^3*r^3 := Nat.mul_le_mul_left _ hD
    _ = (a*b*c*r)^3 := (mul_pow _ _ _).symm
    _ ≤ X^3 := Nat.pow_le_pow_left hX 3

def markedProgressionShortTriples (X : ℕ) : Finset MarkedDivisorTriple :=
  (markedDivisorTripleBox X).filter (fun t => (markedDivisorTripleProduct t)^4 ≤ X^3)

def markedProgressionLastFactors (a X D : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 (X/D)).filter (fun r => Nat.ModEq a (D*r) 1)

theorem markedProgression_quadruple_count (a X : ℕ) :
    (markedProgressionDivisorQuadruples a X).card ≤
      4 * ∑ t ∈ markedProgressionShortTriples X,
        (markedProgressionLastFactors a X (markedDivisorTripleProduct t)).card := by
  let S := (markedProgressionShortTriples X).sigma
    (fun t => markedProgressionLastFactors a X (markedDivisorTripleProduct t))
  let f (t : MarkedDivisorQuadruple) : Fin 4 × (Σ _ : MarkedDivisorTriple, ℕ) :=
    let i := markedDivisorLargestIndex t
    let u := markedDivisorMoveLast i t
    (i,⟨(u.1,u.2.1,u.2.2.1),u.2.2.2⟩)
  calc
    _ ≤ ((Finset.univ : Finset (Fin 4)).product S).card := by
      apply Finset.card_le_card_of_injOn f
      · intro t ht
        obtain ⟨hbox,hprod,hmod⟩ := Finset.mem_filter.mp ht
        let u := markedDivisorMoveLast (markedDivisorLargestIndex t) t
        let v : MarkedDivisorTriple := (u.1,u.2.1,u.2.2.1)
        let D := markedDivisorTripleProduct v
        have he : markedDivisorQuadrupleProduct u = markedDivisorQuadrupleProduct t :=
          markedDivisorMoveLast_product _ _
        obtain ⟨h₁,h₂,h₃,h₄⟩ : t.1∈Finset.Ioc 0 X ∧ t.2.1∈Finset.Ioc 0 X ∧
            t.2.2.1∈Finset.Ioc 0 X ∧ t.2.2.2∈Finset.Ioc 0 X := by
          simpa only [markedDivisorQuadrupleBox,markedDivisorTripleBox,Finset.product_eq_sprod,
            Finset.mem_product] using hbox
        have htpos : 0 < markedDivisorQuadrupleProduct t := Nat.mul_pos
          (Nat.mul_pos (Nat.mul_pos (Finset.mem_Ioc.mp h₁).1 (Finset.mem_Ioc.mp h₂).1)
            (Finset.mem_Ioc.mp h₃).1) (Finset.mem_Ioc.mp h₄).1
        have hpu : markedDivisorQuadrupleProduct u ≤ X := he.symm ▸ hprod
        have hmu : Nat.ModEq a (markedDivisorQuadrupleProduct u) 1 := he.symm ▸ hmod
        have hu : u ∈ markedDivisorQuadrupleBox X := markedDivisorQuadruple_mem_box u
          (he.symm ▸ htpos) hpu
        obtain ⟨hu₁,hu₂,hu₃,hu₄⟩ : u.1∈Finset.Ioc 0 X ∧ u.2.1∈Finset.Ioc 0 X ∧
            u.2.2.1∈Finset.Ioc 0 X ∧ u.2.2.2∈Finset.Ioc 0 X := by
          simpa only [markedDivisorQuadrupleBox,markedDivisorTripleBox,Finset.product_eq_sprod,
            Finset.mem_product] using hu
        have hD : 0 < D := Nat.mul_pos
          (Nat.mul_pos (Finset.mem_Ioc.mp hu₁).1 (Finset.mem_Ioc.mp hu₂).1) (Finset.mem_Ioc.mp hu₃).1
        have hmax := markedDivisorLargestIndex_bounds t
        have hshort : D^4 ≤ X^3 :=
          markedDivisorRetained_pow_le hmax.1 hmax.2.1 hmax.2.2 hpu
        have hv : v ∈ markedProgressionShortTriples X := Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hu₁,Finset.mem_product.mpr ⟨hu₂,hu₃⟩⟩,hshort⟩
        have hr : u.2.2.2 ≤ X/D := (Nat.le_div_iff_mul_le hD).mpr
          ((Nat.mul_comm _ _).trans_le (show D*u.2.2.2≤X from hpu))
        have hlast : u.2.2.2 ∈ markedProgressionLastFactors a X D := Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hu₄).1,hr⟩,hmu⟩
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_sigma.mpr ⟨hv,hlast⟩⟩
      · intro t _ u _ h
        have hi : markedDivisorLargestIndex t = markedDivisorLargestIndex u := congrArg Prod.fst h
        have he : markedDivisorMoveLast (markedDivisorLargestIndex t) t =
            markedDivisorMoveLast (markedDivisorLargestIndex u) u :=
          congrArg (fun z : Fin 4 × (Σ _ : MarkedDivisorTriple, ℕ) =>
            (z.2.1.1,z.2.1.2.1,z.2.1.2.2,z.2.2)) h
        rw [← hi] at he
        exact markedDivisorMoveLast_injective _ he
    _ = _ := by simp only [S,Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,
      Fintype.card_fin,Finset.card_sigma]

end ArtinMatthews
