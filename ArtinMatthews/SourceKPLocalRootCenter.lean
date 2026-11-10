module

public import ArtinMatthews.SourceKPLocalRootWord
public import ArtinMatthews.SourceCubicKPTorus
public import ArtinMatthews.SourceKPLocalBorelRelations
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The elementary root subgroup generates a genuine nontrivial
central cube root. The argument uses the actual local Hilbert
pairing and the noncube class of an actual uniformizer. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory GlobalClassFieldTheory.Reciprocity
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "ν₀" => sourceKPFiniteVal K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P
local notation "H" => sourceFiniteKPHilbert K hζ P

include hζ in
theorem sourceKPLocalRootHilbert_exists_ne_one : ∃ a b : Lˣ, H a b ≠ 1 := by
  obtain ⟨u,hu⟩ := P.intValuation_exists_uniformizer
  let x := algebraMap K L (u : K)
  have hx : ν₀ x = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((u : K) : L) = _
    rw [P.valuedAdicCompletion_eq_valuation', P.valuation_of_algebraMap]
    exact hu
  have hx₀ : x ≠ 0 := by
    intro he
    rw [he,map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  let a := Units.mk0 x hx₀
  have ha : sourceKPValuationOrder ν₀ a = 1 := (sourceKPValuationOrder_eq ν₀ a 1).mpr hx
  have hna : powerClass L 3 a ≠ 1 := by
    intro h
    change (QuotientGroup.mk a : Lˣ ⧸ (powMonoidHom (3 : ℕ) : Lˣ →* Lˣ).range) = 1 at h
    obtain ⟨c,hc⟩ := (QuotientGroup.eq_one_iff a).mp h
    change c^(3 : ℕ) = a at hc
    have horder := sourceKPValuationOrder_zpow ν₀ c (3 : ℤ)
    rw [show (3 : ℤ) = (↑(3 : ℕ) : ℤ) from rfl,zpow_natCast,hc,ha] at horder
    omega
  let hμ := sLocalPrimitiveRoots K 3 (sourceHilbertRootThree_isPrimitive K hζ)
  let B := finitePlaceAdicHilbertPairingFamily K 3 hμ P
  have hnd := (finitePlaceAdicHilbertPairingFamily_isLocallyHilbert K 3 hμ P).2.2.1
  by_contra! he
  apply hna
  apply hnd.1 (powerClass L 3 a)
  intro b
  obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (powMonoidHom (3 : ℕ) : Lˣ →* Lˣ).range b
  change powerClass L 3 y = b at hy
  rw [← hy]
  exact he a y

theorem sourceKPLocalRootDiagonal_commutation (a b : Lˣ) :
    l₀ (sourceGL2Diagonal (a^2)) * l₀ (sourceGL2Diagonal (b^2)) =
      z₀ (H a b) * (l₀ (sourceGL2Diagonal (b^2))*l₀ (sourceGL2Diagonal (a^2))) := by
  have h₁ : H (a^2) (b^2) = H a b := by
    rw [(H).map_pow a 2, MonoidHom.pow_apply, (H a).map_pow b 2, ← pow_mul,
      show (2*2 : ℕ) = 3+1 by decide, pow_add, sourceCubicRoot_cube, one_mul, pow_one]
  have h₂ : H (b^2) (a^2) = (H a b)⁻¹ := by
    rw [sourceFiniteKPHilbert_skew K hζ P (b^2) (a^2), h₁]
  have hphase : H (a^2) (b^2)^2 / H (b^2) (a^2)^2 = H a b := by
    rw [h₁,h₂,inv_pow,div_inv_eq_mul,← pow_add,
      show (2+2 : ℕ) = 3+1 by decide,pow_add,sourceCubicRoot_cube,one_mul,pow_one]
  have h := congrArg Subtype.val (sourceKPLocalBorelDiagonal_commutator K hζ P (a^2) (b^2))
  change l₀ (sourceGL2Diagonal (a^2)) * l₀ (sourceGL2Diagonal (b^2)) =
    z₀ (H (a^2) (b^2)^2 / H (b^2) (a^2)^2) *
      (l₀ (sourceGL2Diagonal (b^2))*l₀ (sourceGL2Diagonal (a^2))) at h
  rwa [hphase] at h

theorem sourceKPLocalRootCenter_mem (a b : Lˣ) :
    z₀ (H a b) ∈ sourceKPLocalRootSubgroup K hζ P := by
  let A := sourceKPLocalRootDiagonalWord K hζ P a
  let B := sourceKPLocalRootDiagonalWord K hζ P b
  let p := l₀ (sourceGL2Diagonal (a^2))
  let q := l₀ (sourceGL2Diagonal (b^2))
  let z := z₀ (H a b)
  obtain ⟨r,hr⟩ := sourceKPLocalRootDiagonalWord_eq_center_mul K hζ P a
  obtain ⟨t,ht⟩ := sourceKPLocalRootDiagonalWord_eq_center_mul K hζ P b
  have hr' : A = z₀ r*p := hr
  have ht' : B = z₀ t*q := ht
  have hswap (r₁ t₁ : rootsOfUnity 3 L) (x y : G) :
      (z₀ r₁*x)*(z₀ t₁*y) = (z₀ r₁*z₀ t₁)*(x*y) :=
    (sourceFiniteKP2ProjectiveCenter_commute K hζ P t₁ x).symm.mul_mul_mul_comm (z₀ r₁) y
  have hab : A*B = z*(B*A) := calc
    _ = (z₀ r*z₀ t)*(p*q) := by rw [hr',ht',hswap]
    _ = (z₀ r*z₀ t)*(z*(q*p)) :=
      congrArg ((z₀ r*z₀ t)*·) (sourceKPLocalRootDiagonal_commutation K hζ P a b)
    _ = z*((z₀ t*z₀ r)*(q*p)) := by
      rw [(sourceFiniteKP2ProjectiveCenter_commute K hζ P (H a b) _).symm.left_comm,
        (sourceFiniteKP2ProjectiveCenter_commute K hζ P r (z₀ t)).eq]
    _ = _ := by rw [hr',ht',hswap]
  let U := sourceKPLocalRootSubgroup K hζ P
  have hA : A ∈ U := sourceKPLocalRootDiagonalWord_mem K hζ P a
  have hB : B ∈ U := sourceKPLocalRootDiagonalWord_mem K hζ P b
  have h := U.mul_mem (U.mul_mem hA hB) (U.inv_mem (U.mul_mem hB hA))
  change A*B*(B*A)⁻¹ ∈ U at h
  rwa [hab,mul_inv_cancel_right] at h

theorem sourceKPLocalRootCenter_exists :
    ∃ z : rootsOfUnity 3 L, z ≠ 1 ∧ z₀ z ∈ sourceKPLocalRootSubgroup K hζ P := by
  obtain ⟨a,b,hab⟩ := sourceKPLocalRootHilbert_exists_ne_one K hζ P
  exact ⟨H a b, hab, sourceKPLocalRootCenter_mem K hζ P a b⟩

end
end ArtinMatthews
