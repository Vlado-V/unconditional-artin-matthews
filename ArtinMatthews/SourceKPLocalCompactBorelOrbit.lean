module

public import ArtinMatthews.SourceKPLocalCompactRestriction
public import ArtinMatthews.SourceKPLocalBorelEmbedding
public import ArtinMatthews.SourceKPTameBorelValues
public import ArtinMatthews.SourceKPLocalBorelRelations
public import ArtinMatthews.SourceKPLocalTorusCharacter
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
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
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness


set_option backward.privateInPublic true
@[expose] public section

/-! At every finite place the actual global torus value representation
has finite local Borel cyclic spans. The indexing quotient is the
actual local cube-class group. Cubes and the cubic center act by the
derived global inducing scalars, including at ramified places. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain LocalFieldTheory QuadraticWeil
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "B" => SourceFiniteKPProjectiveBorel K hζ P
local notation "d₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P
local notation "n₀" => sourceFiniteKPProjectiveBorelUpper K hζ P
local notation "z₀" => sourceFiniteKPProjectiveBorelCenter K hζ P
local notation "ρ₀" => sourceKPAdelicLocalBorelRepresentation K hζ P
local notation "V₀" => SourceKPAdelicTorusInducedSpace K hζ

abbrev SourceKPLocalCompactCubeClasses := Lˣ ⧸ (powMonoidHom (3 : ℕ) : Lˣ →* Lˣ).range

local instance sourceKPLocalCompactGlobalTorusAddCommGroup (s : ℂ) : AddCommGroup (V₀ s) :=
  Submodule.addCommGroup _

theorem sourceKPLocalCompactCubeClasses_finite : Finite (SourceKPLocalCompactCubeClasses K P) := by
  let : ValuativeRel L := adicRelation K P
  let : IsNonarchimedeanLocalField L := adicLocalField K P
  exact finite_nthPowerQuotient_of_natCast_ne_zero L 3 (by norm_num)

def sourceKPLocalCompactBorelOrbit (s : ℂ) (v : V₀ s) : Submodule ℂ (V₀ s) :=
  Submodule.span ℂ (Set.range (fun b : B => ρ₀ s b v))

local instance sourceKPLocalCompactBorelOrbitAddCommGroup (s : ℂ) (v : V₀ s) :
    AddCommGroup (sourceKPLocalCompactBorelOrbit K hζ P s v) := Submodule.addCommGroup _

theorem sourceKPLocalCompactBorelOrbit_invariant (s : ℂ) (v : V₀ s) (b : B)
    (x : V₀ s) (hx : x ∈ sourceKPLocalCompactBorelOrbit K hζ P s v) :
    ρ₀ s b x ∈ sourceKPLocalCompactBorelOrbit K hζ P s v := by
  change x ∈ Submodule.span ℂ (Set.range (fun a : B => ρ₀ s a v)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨b*a,?_⟩
    change ρ₀ s (b*a) v = ρ₀ s b (ρ₀ s a v)
    rw [map_mul]
    rfl
  | zero => simpa only [map_zero] using (sourceKPLocalCompactBorelOrbit K hζ P s v).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (sourceKPLocalCompactBorelOrbit K hζ P s v).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (sourceKPLocalCompactBorelOrbit K hζ P s v).smul_mem a hx

theorem sourceKPLocalCompactBorelOrbit_eq_cube_span (s : ℂ) (v : V₀ s) :
    sourceKPLocalCompactBorelOrbit K hζ P s v =
      Submodule.span ℂ (Set.range (fun c : SourceKPLocalCompactCubeClasses K P => ρ₀ s (d₀ c.out) v)) := by
  let T : Submodule ℂ (V₀ s) :=
    Submodule.span ℂ (Set.range (fun c : SourceKPLocalCompactCubeClasses K P => ρ₀ s (d₀ c.out) v))
  have hdiag (y : Lˣ) : ρ₀ s (d₀ y) v ∈ T := by
    let c : SourceKPLocalCompactCubeClasses K P := QuotientGroup.mk y
    let a := c.out
    have hq : (QuotientGroup.mk a : SourceKPLocalCompactCubeClasses K P) = QuotientGroup.mk y :=
      QuotientGroup.out_eq' c
    obtain ⟨b,hb⟩ := QuotientGroup.eq.mp hq
    change b^(3 : ℕ) = a⁻¹*y at hb
    have he : a*b^3 = y := by rw [hb,mul_inv_cancel_left]
    have hd : d₀ y = d₀ a*d₀ (b^3) := by
      rw [sourceKPLocalBorelDiagonal_mul K hζ P,
        sourceFiniteKPHilbert_cube_right K hζ P,one_pow,he]
      have hz : sourceFiniteKPProjectiveBorelCenter K hζ P 1 = 1 := by
        apply Subtype.ext
        exact map_one _
      rw [hz,one_mul]
    rw [hd,map_mul,Module.End.mul_apply,sourceKPAdelicLocalBorelRepresentation_cube K hζ P,
      map_smul]
    exact T.smul_mem _ (Submodule.subset_span ⟨c,rfl⟩)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨b,rfl⟩
    obtain ⟨z,x,y,hb⟩ := sourceFiniteKPProjectiveBorel_factor K hζ P b
    have he : b = z₀ z*n₀ x*d₀ y := Subtype.ext hb
    change ρ₀ s b v ∈ T
    rw [he,map_mul,Module.End.mul_apply,map_mul,Module.End.mul_apply,
      sourceKPAdelicLocalBorelRepresentation_upper K hζ P,
      sourceKPAdelicLocalBorelRepresentation_center K hζ P]
    exact T.smul_mem _ (hdiag y)
  · apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    exact Submodule.subset_span ⟨d₀ c.out,rfl⟩

theorem sourceKPLocalCompactBorelOrbit_finiteDimensional (s : ℂ) (v : V₀ s) :
    FiniteDimensional ℂ (sourceKPLocalCompactBorelOrbit K hζ P s v) := by
  let : Finite (SourceKPLocalCompactCubeClasses K P) := sourceKPLocalCompactCubeClasses_finite K P
  change Module.Finite ℂ (sourceKPLocalCompactBorelOrbit K hζ P s v)
  rw [sourceKPLocalCompactBorelOrbit_eq_cube_span K hζ P s v]
  exact Module.Finite.span_of_finite ℂ (Set.finite_range _)

def sourceKPLocalCompactBorelOrbitRepresentation (s : ℂ) (v : V₀ s) :
    Representation ℂ B (sourceKPLocalCompactBorelOrbit K hζ P s v) where
  toFun b := (ρ₀ s b).restrict (sourceKPLocalCompactBorelOrbit_invariant K hζ P s v b)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ρ₀ s 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' b a := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ρ₀ s (b*a) x.val = ρ₀ s b (ρ₀ s a x.val)
    rw [map_mul]
    rfl

theorem sourceKPLocalCompactBorelOrbitFixed_finiteDimensional (s : ℂ) (v : V₀ s) :
    FiniteDimensional ℂ (sourceKPLocalCompactFixedSpace K hζ P
      (sourceKPLocalCompactBorelOrbitRepresentation K hζ P s v)) := by
  let : FiniteDimensional ℂ (sourceKPLocalCompactBorelOrbit K hζ P s v) :=
    sourceKPLocalCompactBorelOrbit_finiteDimensional K hζ P s v
  exact sourceKPLocalCompactFixedSpace_finiteDimensional K hζ P _

end
end ArtinMatthews
