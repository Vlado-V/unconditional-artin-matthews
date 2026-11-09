module

public import ArtinMatthews.SourceKPJacquetBallCancellation
public import ArtinMatthews.SourceAlgebraicInduction
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.SourceJacquetFiniteUpperQuotient
public import ArtinMatthews.CompactFiniteAverage
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


set_option backward.privateInPublic true
@[expose] public section

/-! The finite upper-root quotient average on a right-stable induced
subspace is the actual self-dual Haar integral in finite coordinates. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical QuadraticWeil MeasureTheory Filter
open scoped NumberField SourcePhysical Classical BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "n₋" => fun t : L => l₀ (sourceGL2Lower t)
local notation "ψ₀" => localFiniteCharacter K P
local notation "ν₀" => sourceLocalValuation K P
local notation "B" => sourceLocalBall K P
local notation "μ₀" => sourceLocalSelfDual K P

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    (C : Submodule ℂ (sourceAlgebraicInducedSpace _ ρ))

/-- The small upper and lower right-root neighborhoods used by smoothness. -/
def SourceKPJacquetRootSmooth : Prop :=
  ∀ f : C, ∃ M : ℕ, ∀ t ∈ B (-(M : ℤ)), ∀ g : G,
    f.val.val (g * n₀ t) = f.val.val g ∧ f.val.val (g * n₋ t) = f.val.val g

variable (hC : ∀ (g : SourceFiniteKP2Projective K hζ P) (f : sourceAlgebraicInducedSpace _ ρ),
    f ∈ C → sourceAlgebraicInducedRepresentation (SourceFiniteKPProjectiveBorel K hζ P) ρ g f ∈ C)

def sourceKPJacquetRight (g : G) : C →ₗ[ℂ] C :=
  (sourceAlgebraicInducedRepresentation B₀ ρ g).restrict (hC g)

local notation "r₀" => sourceKPJacquetRight K hζ P ρ C hC

theorem sourceKPJacquetRight_eval (g k : G) (f : C) : (r₀ g f).val.val k = f.val.val (k * g) := rfl

variable {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))

def sourceKPJacquetCoordinateEval (g : G) : C →ₗ[ℂ] (ι → ℂ) where
  toFun f := e (f.val.val g)
  map_add' f f' := by
    change e (f.val.val g + f'.val.val g) = _
    exact map_add e _ _
  map_smul' a f := by
    change e (a • f.val.val g) = _
    exact map_smul e _ _

def sourceKPJacquetCoordinateIntegrand (f : C) (g : G) (t : L) : ι → ℂ :=
  ψ₀ (-t) • e (f.val.val (g * n₀ t))

local notation "E₀" => sourceKPJacquetCoordinateIntegrand K hζ P ρ C e

theorem sourceKPJacquetCoordinateIntegrand_eq_of_small (f : C) (g : G) (M : ℕ)
    (hfix : ∀ u ∈ B (-(M : ℤ)), ∀ k : G, f.val.val (k * n₀ u) = f.val.val k)
    (x t : L) (ht : t - x ∈ B (-(M : ℤ))) : E₀ f g t = E₀ f g x := by
  let u := t - x
  have hu : ν₀ u ≤ 1 := ht.trans (by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega))
  have hneg : -u ∈ P.adicCompletionIntegers K := by
    change ν₀ (-u) ≤ 1
    rw [Valuation.map_neg]
    exact hu
  have hψ : ψ₀ (-t) = ψ₀ (-x) := by
    have hsum : -t = -x + -u := by dsimp [u]; abel
    rw [hsum, AddChar.map_add_eq_mul, localFiniteCharacter_integral K P (-u) hneg, mul_one]
  have hf := hfix u ht (g * n₀ x)
  have hxu : x + u = t := by dsimp [u]; abel
  rw [mul_assoc, sourceFiniteKP2ProjectiveLift_upper_add, hxu] at hf
  unfold sourceKPJacquetCoordinateIntegrand
  rw [hψ, hf]

theorem sourceKPJacquetCoordinateIntegrand_continuous (f : C) (g : G) (M : ℕ)
    (hfix : ∀ u ∈ B (-(M : ℤ)), ∀ k : G, f.val.val (k * n₀ u) = f.val.val k) :
    Continuous (E₀ f g) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_const.congr_of_eventuallyEq
  have hU : IsOpen ((fun u : L => u - t) ⁻¹' B (-(M : ℤ))) :=
    (sourceLocalBall_isOpen K P _).preimage (continuous_id.sub continuous_const)
  have ht : t ∈ (fun u : L => u - t) ⁻¹' B (-(M : ℤ)) := by
    change ν₀ (t - t) ≤ _
    rw [sub_self, map_zero]
    exact zero_le
  filter_upwards [hU.mem_nhds ht] with u hu
  exact sourceKPJacquetCoordinateIntegrand_eq_of_small K hζ P ρ C e f g M hfix t u hu

def sourceKPJacquetUpperAverage (R M : ℕ) (f : C) : C := by
  let A := SourceJacquetUpperQuotient K P R M
  letI : Finite A := sourceJacquetUpperQuotient_finite K P R M
  letI : Fintype A := Fintype.ofFinite A
  let rep (a : A) : L := sourceJacquetUpperRepresentative K P R M a
  exact (Fintype.card A : ℂ)⁻¹ • ∑ a : A, ψ₀ (-rep a) • r₀ (n₀ (rep a)) f

local notation "Av" => sourceKPJacquetUpperAverage K hζ P ρ C hC

theorem sourceKPJacquetUpperAverage_eval_integral (R M : ℕ) (f : C) (g : G)
    (hfix : ∀ u ∈ B (-(M : ℤ)), ∀ k : G, f.val.val (k * n₀ u) = f.val.val k) :
    ((μ₀).real (B (R : ℤ)) : ℂ) • e ((Av R M f).val.val g) =
      ∫ t in B (R : ℤ), E₀ f g t ∂μ₀ := by
  let U := sourceJacquetUpperBall K P R
  let A := SourceJacquetUpperQuotient K P R M
  let : Finite A := sourceJacquetUpperQuotient_finite K P R M
  let : Fintype A := Fintype.ofFinite A
  let : (μ₀).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  let rep (a : A) : U := sourceJacquetUpperRepresentative K P R M a
  let r := sourceJacquetUpperReduction K P R M
  have hr : Function.Surjective r := sourceJacquetUpperReduction_surjective K P R M
  have hU : IsCompact (U : Set L) := sourceLocalBall_isCompact K P (R : ℤ)
  have hc : Continuous (E₀ f g) := sourceKPJacquetCoordinateIntegrand_continuous K hζ P ρ C e f g M hfix
  have hi : IntegrableOn (E₀ f g) (U : Set L) μ₀ := hc.continuousOn.integrableOn_compact hU
  have hfactor (t : U) : E₀ f g (t : L) = E₀ f g (rep (r t) : L) := by
    have h := sourceJacquetUpperRepresentative_class K P R M (r t)
    have ht : (rep (r t) : L) - (t : L) ∈ B (-(M : ℤ)) :=
      (sourceJacquetUpperReduction_eq_iff K P R M t (rep (r t))).mp h.symm
    exact (sourceKPJacquetCoordinateIntegrand_eq_of_small K hζ P ρ C e f g M hfix t (rep (r t)) ht).symm
  let ev := sourceKPJacquetCoordinateEval K hζ P ρ C e g
  have hev : ev (Av R M f) = (Fintype.card A : ℂ)⁻¹ • ∑ a : A, E₀ f g (rep a : L) := by
    unfold sourceKPJacquetUpperAverage
    rw [map_smul, map_sum]
    apply congrArg ((Fintype.card A : ℂ)⁻¹ • ·)
    apply Finset.sum_congr rfl
    intro a _
    rw [map_smul]
    rfl
  change ((μ₀).real (U : Set L) : ℂ) • ev (Av R M f) = ∫ t in (U : Set L), E₀ f g t ∂μ₀
  rw [hev]
  funext i
  let pr : (ι → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  have hproj := pr.integral_comp_comm hi
  change (∫ t in (U : Set L), E₀ f g t i ∂μ₀) = (∫ t in (U : Set L), E₀ f g t ∂μ₀) i at hproj
  rw [← hproj]
  have hI := compact_finite_integral μ₀ U hU r hr (fun a => E₀ f g (rep a : L) i)
    (fun t => E₀ f g t i) (pr.continuous.comp hc) (fun t => congrFun (hfactor t) i)
  rw [hI]
  change ((μ₀).real (U : Set L) : ℂ) * ((Fintype.card A : ℂ)⁻¹ * (∑ a : A, E₀ f g (rep a : L)) i) = _
  rw [Finset.sum_apply, div_eq_mul_inv]
  ring

theorem sourceKPJacquetUpperAverage_whittaker (R M : ℕ) (f : C) (ℓ : C →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : L) (u : C), ℓ (r₀ (n₀ x) u) = ψ₀ x * ℓ u) :
    ℓ (Av R M f) = ℓ f := by
  let A := SourceJacquetUpperQuotient K P R M
  let : Finite A := sourceJacquetUpperQuotient_finite K P R M
  let : Fintype A := Fintype.ofFinite A
  let rep (a : A) : L := sourceJacquetUpperRepresentative K P R M a
  unfold sourceKPJacquetUpperAverage
  rw [map_smul, map_sum]
  have hterm (a : A) : ℓ (ψ₀ (-rep a) • r₀ (n₀ (rep a)) f) = ℓ f := by
    rw [map_smul, hℓ]
    change ψ₀ (-rep a) * (ψ₀ (rep a) * ℓ f) = ℓ f
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  change (Fintype.card A : ℂ)⁻¹ • (∑ a : A, ℓ (ψ₀ (-rep a) • r₀ (n₀ (rep a)) f)) = ℓ f
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card A : ℂ) ≠ 0), one_mul]

end
end ArtinMatthews
