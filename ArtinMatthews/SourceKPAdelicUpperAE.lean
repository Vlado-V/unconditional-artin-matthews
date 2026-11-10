module

public import ArtinMatthews.SourceKPCuspRepresentativeHaar
public import ArtinMatthews.SourceKPAutomorphicParametricContinuity
public import ArtinMatthews.SourceKPCuspUpperAction
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
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation


set_option backward.privateInPublic true
@[expose] public section

/-! Archimedean upper-root invariance extends to the actual adelic upper root
on finite representatives by rational automorphy and strong approximation. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "G" => PGL(2, InfiniteAdeleRing K)
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "X" => SourceKPFiniteLevelSpace K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "N" => sourceKPAdelicUpperLift K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "Q" => sourceKPFiniteLevelToCompact K hζ
local notation "ν" => sourceKPFiniteRepresentativeHaar K hζ
local notation "μ" => sourceKPArchHaar K hζ

theorem sourceKPFiniteLevelToCompact_rational (γ : PGL(2, K)) (x : X) :
    Q (γ • x) = Q x := by
  apply congrArg (sourceKPAutomorphicCompactMk K hζ)
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩

theorem sourceKPCuspFiniteUpper_rational_label (b : F) (u : 𝔸ᶠ[K]) :
    ∃ r : K, sourceKPRationalFiniteMap K hζ (sourcePGL2Upper r) • b = Nf u • b := by
  let S : Set (𝔸ᶠ[K]) := (fun v => Nf v • b) ⁻¹' {Nf u • b}
  have hS : IsOpen S :=
    (isOpen_discrete _).preimage (sourceKPCuspFiniteUpper_continuous K hζ b)
  have hd : DenseRange (algebraMap K 𝔸ᶠ[K]) :=
    OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles K
  obtain ⟨r, hr⟩ := hd.exists_mem_open hS ⟨u, rfl⟩
  refine ⟨r, ?_⟩
  change sourceKPFiniteAdeleProjectiveRationalLift K hζ (sourcePGL2Upper r) • b = Nf u • b
  rw [← sourceKPFiniteAdeleUpperLift_rational]
  exact hr

theorem sourceKPAdelicUpper_compact_absorb_finite (u : 𝔸[K]) (b : F) :
    ∃ v : InfiniteAdeleRing K, ∀ a : G,
      Q (N u • (a,b)) = Q (N ((v,0) : 𝔸[K]) • (a,b)) := by
  obtain ⟨r,hr⟩ := sourceKPCuspFiniteUpper_rational_label K hζ b u.2
  let v := u.1 - algebraMap K (InfiniteAdeleRing K) r
  refine ⟨v, fun a => ?_⟩
  let w : 𝔸[K] := (v,0)
  have he : algebraMap K 𝔸[K] r + w = ((u.1, algebraMap K 𝔸ᶠ[K] r) : 𝔸[K]) := by
    apply Prod.ext
    · change algebraMap K (InfiniteAdeleRing K) r + v = u.1
      dsimp only [v]
      abel
    · change algebraMap K 𝔸ᶠ[K] r + 0 = algebraMap K 𝔸ᶠ[K] r
      exact add_zero _
  have hsame : N u • ((a,b) : X) = N (algebraMap K 𝔸[K] r + w) • ((a,b) : X) := by
    rw [he]
    have hf : Nf u.2 • b = Nf (algebraMap K 𝔸ᶠ[K] r) • b := by
      rw [sourceKPFiniteAdeleUpperLift_rational]
      exact hr.symm
    exact congrArg (fun c : F =>
      (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) u.1) * a,c)) hf
  calc
    Q (N u • (a,b)) = Q (N (algebraMap K 𝔸[K] r + w) • (a,b)) := congrArg Q hsame
    _ = Q (N w • (a,b)) := by
      rw [sourceKPAdelicUpperLift_add, sourceKPAdelicUpperLift_rational, mul_smul]
      exact sourceKPFiniteLevelToCompact_rational K hζ (sourcePGL2Upper r) (N w • (a,b))

theorem sourceKPFiniteRepresentative_ae_iff_slices (p : X → Prop) :
    (∀ᵐ x ∂ν, p x) ↔ ∀ b : F, ∀ᵐ a ∂μ, p (a,b) := by
  constructor
  · intro h b
    have hs : ∀ᵐ a ∂μ, ∀ᵐ c ∂(Measure.count : Measure F), p (a,c) :=
      Measure.ae_ae_of_ae_prod h
    exact hs.mono fun _ ha => (Measure.ae_count_iff.mp ha) b
  · intro h
    have hall : ∀ᵐ a ∂μ, ∀ b : F, p (a,b) := ae_all_iff.mpr h
    exact (Measure.quasiMeasurePreserving_fst.ae hall).mono fun x hx => hx x.2

theorem sourceKPAdelicUpper_ae_of_arch_slice {B : Type*} (W : Y → B)
    (harch : ∀ (v : InfiniteAdeleRing K) (b : F), ∀ᵐ a ∂μ,
      W (Q (N ((v,0) : 𝔸[K]) • (a,b))) = W (Q (a,b))) (u : 𝔸[K]) :
    ∀ᵐ x ∂ν, W (Q (N u • x)) = W (Q x) := by
  apply (sourceKPFiniteRepresentative_ae_iff_slices K hζ _).mpr
  intro b
  obtain ⟨v,hv⟩ := sourceKPAdelicUpper_compact_absorb_finite K hζ u b
  filter_upwards [harch v b] with a ha
  exact (congrArg W (hv a)).trans ha

theorem sourceKPAdelicUpper_ae_of_arch {B : Type*} (W : Y → B)
    (harch : ∀ v : InfiniteAdeleRing K, ∀ᵐ x ∂ν,
      W (Q (N ((v,0) : 𝔸[K]) • x)) = W (Q x)) (u : 𝔸[K]) :
    ∀ᵐ x ∂ν, W (Q (N u • x)) = W (Q x) :=
  sourceKPAdelicUpper_ae_of_arch_slice K hζ W
    (fun v => (sourceKPFiniteRepresentative_ae_iff_slices K hζ _).mp (harch v)) u

theorem sourceKPAdelicUpper_ae_of_arch_cover_slice {B : Type*} (W : Y → B)
    (harch : ∀ (v : InfiniteAdeleRing K) (qf : Gf), ∀ᵐ a ∂μ,
      W (sourceKPAutomorphicCompactMk K hζ
          (sourceKPAutomorphicLevelMk K hζ (N ((v,0) : 𝔸[K]) * (a,qf)))) =
        W (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ (a,qf))))
    (u : 𝔸[K]) :
    ∀ᵐ x ∂ν, W (Q (N u • x)) = W (Q x) := by
  apply sourceKPAdelicUpper_ae_of_arch_slice K hζ W _ u
  intro v b
  obtain ⟨qf,rfl⟩ := QuotientGroup.mk_surjective b
  filter_upwards [harch v qf] with a ha
  change W (Q (N ((v,0) : 𝔸[K]) • sourceKPFiniteLevelMk K hζ (a,qf))) =
    W (Q (sourceKPFiniteLevelMk K hζ (a,qf)))
  rw [← sourceKPFiniteLevelMk_mul]
  exact ha

theorem sourceKPFiniteUpper_ae_of_arch {B : Type*} (W : Y → B)
    (harch : ∀ v : InfiniteAdeleRing K, ∀ᵐ x ∂ν,
      W (Q (N ((v,0) : 𝔸[K]) • x)) = W (Q x)) (u : 𝔸ᶠ[K]) :
    ∀ᵐ x ∂ν, W (Q (x.1,Nf u • x.2)) = W (Q x) := by
  have h := sourceKPAdelicUpper_ae_of_arch K hζ W harch ((0,u) : 𝔸[K])
  filter_upwards [h] with x hx
  change W (Q (ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) 0) * x.1,
    Nf u • x.2)) = W (Q x) at hx
  simpa only [sourceKPUpperMatrix_zero,map_one,one_mul] using hx

end
end ArtinMatthews
