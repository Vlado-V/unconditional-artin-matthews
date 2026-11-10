module

public import Mathlib.Data.Int.ModEq
public import ArtinMatthews.MarkedMinorArcSharedLattice
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual dirty-edge residue and anchor congruence from PD §4. The residue
is independent of the omission tuple and the other promoted primes. -/
namespace ArtinMatthews

/-- The actual dirty determinant in the source raw row rule. -/
def markedMinorDirtyDeterminant (P D : ℤ) (p : ℕ) (Z T : ℤ) : ℤ :=
  P-D*(p : ℤ)*Z*T

/-- Its residue depends only on the source full product. -/
theorem markedMinorDirtyDeterminant_cast (P D : ℤ) (p : ℕ) (Z T : ℤ) :
    (markedMinorDirtyDeterminant P D p Z T : ZMod p)=(P : ZMod p) := by
  simp [markedMinorDirtyDeterminant]

/-- Literal target position h*z+j*w. -/
def markedMinorDirtyPosition (z w : ℤ × ℤ) (h j : ℤ) : ℤ × ℤ :=
  (h*z.1+j*w.1,h*z.2+j*w.2)

theorem markedMinorDirtyPosition_det (z w : ℤ × ℤ) (h₁ j₁ h₂ j₂ : ℤ) :
    markedMinorIntegerDet (markedMinorDirtyPosition z w h₁ j₁)
      (markedMinorDirtyPosition z w h₂ j₂) =
      (h₁*j₂-j₁*h₂)*markedMinorIntegerDet z w := by
  unfold markedMinorDirtyPosition markedMinorIntegerDet
  ring

/-- The literal nonzero projective scalar relation is symmetric over the
actual prime residue field. -/
theorem markedMinorSamePrimeLine_symm {p : ℕ} (hp : p.Prime) {z v : ℤ × ℤ}
    (h : MarkedMinorSamePrimeLine p z v) : MarkedMinorSamePrimeLine p v z := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c,hc,h₁,h₂⟩ := h
  refine ⟨c⁻¹,inv_ne_zero hc,?_,?_⟩
  · rw [h₁,← mul_assoc,inv_mul_cancel₀ hc,one_mul]
  · rw [h₂,← mul_assoc,inv_mul_cancel₀ hc,one_mul]

theorem markedMinorSamePrimeLine_trans {p : ℕ} (hp : p.Prime) {z v w : ℤ × ℤ}
    (h : MarkedMinorSamePrimeLine p z v) (h' : MarkedMinorSamePrimeLine p v w) :
    MarkedMinorSamePrimeLine p z w := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c,hc,h₁,h₂⟩ := h
  obtain ⟨d,hd,h₃,h₄⟩ := h'
  exact ⟨d*c,mul_ne_zero hd hc,by rw [h₃,h₁,mul_assoc],by rw [h₄,h₂,mul_assoc]⟩

/-- The actual fixed anchor line determines a single residue of h, uniformly
in D,Z and the fresh outside-group product T. -/
theorem markedMinorDirty_anchor_residue_unique {p : ℕ} (hp : p.Prime)
    (P D₁ D₂ Z₁ Z₂ T₁ T₂ h₁ h₂ : ℤ) (hP : ¬(p : ℤ) ∣ P)
    (z w : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hline : MarkedMinorSamePrimeLine p
      (markedMinorDirtyPosition z w h₁ (markedMinorDirtyDeterminant P D₁ p Z₁ T₁))
      (markedMinorDirtyPosition z w h₂ (markedMinorDirtyDeterminant P D₂ p Z₂ T₂))) :
    (h₁ : ZMod p)=(h₂ : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hj := markedMinorSamePrimeLine_dvd p _ _ hline
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hj
  rw [markedMinorDirtyPosition_det,hd,mul_one] at hz
  simp only [Int.cast_sub,Int.cast_mul,markedMinorDirtyDeterminant_cast] at hz
  have he : (P : ZMod p)*((h₁ : ZMod p)-(h₂ : ZMod p))=0 := by
    linear_combination hz
  have hP₀ : (P : ZMod p) ≠ 0 := by
    intro hh
    exact hP ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh)
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hP₀)

/-- Two actual hits at one fixed anchor line determine the same h residue,
uniformly over the other dirty-edge numeric choices. -/
theorem markedMinorDirty_anchor_residue_unique_of_anchor {p : ℕ} (hp : p.Prime)
    (P D₁ D₂ Z₁ Z₂ T₁ T₂ h₁ h₂ : ℤ) (hP : ¬(p : ℤ) ∣ P)
    (z w anchor : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (h₁a : MarkedMinorSamePrimeLine p
      (markedMinorDirtyPosition z w h₁ (markedMinorDirtyDeterminant P D₁ p Z₁ T₁)) anchor)
    (h₂a : MarkedMinorSamePrimeLine p
      (markedMinorDirtyPosition z w h₂ (markedMinorDirtyDeterminant P D₂ p Z₂ T₂)) anchor) :
    (h₁ : ZMod p)=(h₂ : ZMod p) :=
  markedMinorDirty_anchor_residue_unique hp P D₁ D₂ Z₁ Z₂ T₁ T₂ h₁ h₂ hP z w hd
    (markedMinorSamePrimeLine_trans hp h₁a (markedMinorSamePrimeLine_symm hp h₂a))

/-- The exact source neighbor formula and the determined h residue yield
PD's actual anchor interval of radius16/p. -/
theorem markedMinorDirty_anchor_proximity (P D Z T h hstar : ℤ) {p : ℕ}
    (hp : 0 < p) (r : ℝ) (hh : Int.ModEq (p : ℤ) h hstar)
    (hbox : |(h : ℝ)+(markedMinorDirtyDeterminant P D p Z T : ℝ)*r| ≤ 16) :
    ‖(((D : ℝ)*Z*T*r-((P : ℝ)*r+hstar)/p : ℝ) : AddCircle (1:ℝ))‖ ≤ 16/(p : ℝ) := by
  have hpr : (0:ℝ) < p := by exact_mod_cast hp
  obtain ⟨k,hk⟩ := hh.symm.dvd
  have heh : h=hstar+(p : ℤ)*k := by omega
  have he : (D : ℝ)*Z*T*r-((P : ℝ)*r+hstar)/p =
      (k : ℝ)-((h : ℝ)+(markedMinorDirtyDeterminant P D p Z T : ℝ)*r)/p := by
    rw [heh]
    unfold markedMinorDirtyDeterminant
    push_cast
    field_simp
    ring
  rw [he]
  have hres : (((k : ℝ)-((h : ℝ)+(markedMinorDirtyDeterminant P D p Z T : ℝ)*r)/p : ℝ) : AddCircle (1:ℝ)) =
      (-(((h : ℝ)+(markedMinorDirtyDeterminant P D p Z T : ℝ)*r)/p) : ℝ) := by
    rw [sub_eq_add_neg,AddCircle.coe_add]
    have hk₀ : ((k : ℝ) : AddCircle (1:ℝ))=0 := by
      have hh := AddSubgroup.zsmul_mem_zmultiples (1:ℝ) k
      rw [zsmul_eq_mul,mul_one] at hh
      exact (QuotientAddGroup.eq_zero_iff _).mpr hh
    rw [hk₀,zero_add]
  rw [hres]
  calc
    _ ≤ |-(((h : ℝ)+(markedMinorDirtyDeterminant P D p Z T : ℝ)*r)/p)| :=
      QuotientAddGroup.norm_mk_le_norm
    _ = |(h : ℝ)+(markedMinorDirtyDeterminant P D p Z T : ℝ)*r|/(p : ℝ) := by
      rw [abs_neg,abs_div,abs_of_pos hpr]
    _ ≤ _ := div_le_div_of_nonneg_right hbox hpr.le

end ArtinMatthews
