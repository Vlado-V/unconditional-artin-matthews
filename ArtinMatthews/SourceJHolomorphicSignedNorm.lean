module

public import ArtinMatthews.SourceJHolomorphicHilbert
public import ArtinMatthews.SpectralPeterssonSourcePackets
public import ArtinMatthews.SpectralPeterssonPhysicalCauchy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The signed source packet norms are the literal native Petersson
integrals. Reflection conjugates the finite packet coefficients. -/
namespace ArtinMatthews
open Set Filter MeasureTheory UpperHalfPlane
open scoped MatrixGroups BigOperators ComplexConjugate
noncomputable section

private theorem signed_vector_norm (negative : Bool) (F : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) : ‖spectralPeterssonSignVector negative F z‖ = ‖F z‖ := by
  cases negative <;> simp [spectralPeterssonSignVector,Complex.norm_conj]

private theorem signed_packet_value {ι : Type*} (N k : ℕ) [NeZero N]
    (negative : Bool) (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (z : UpperHalfPlane) :
    (∑ i ∈ v, α i*spectralPeterssonSignVector negative
      (gamma0PeterssonSourceInfinity N k (m i)) z) =
    spectralPeterssonSignVector negative
      (gamma0PeterssonSourceInfinityPacket N k v (fun i => if negative then conj (α i) else α i) m) z := by
  cases negative <;>
    simp [spectralPeterssonSignVector,gamma0PeterssonSourceInfinityPacket,map_sum,map_mul]

theorem sourceJHolomorphicInfinityPacketL2_coe {ι : Type*} (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) :
    ⇑(sourceJHolomorphicInfinityPacketL2 N k hk hEven negative v α m)
      =ᵐ[volume.restrict (gamma0InteriorRegion N)]
      spectralPeterssonHilbertProfile k (spectralPeterssonSignVector negative
        (gamma0PeterssonSourceInfinityPacket N k v (fun i => if negative then conj (α i) else α i) m)) := by
  let V (i : ι) := gamma0PeterssonSourceInfinityL2 N k hk hEven negative (m i)
  let W (i : ι) := spectralPeterssonHilbertProfile k
    (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity N k (m i)))
  let μ := volume.restrict (gamma0InteriorRegion N)
  have h₁ : ⇑(sourceJHolomorphicInfinityPacketL2 N k hk hEven negative v α m)
      =ᵐ[μ] ∑ i ∈ v, ⇑(α i • V i) := Lp.coeFn_finsetSum v _
  have h₂ : (∑ i ∈ v, ⇑(α i • V i)) =ᵐ[μ] ∑ i ∈ v, α i • W i := by
    apply eventuallyEq_sum
    intro i _
    exact (Lp.coeFn_smul (α i) (V i)).trans
      ((gamma0PeterssonSourceInfinityL2_coe N k hk hEven negative (m i)).fun_comp
        (fun w : ℂ => α i • w))
  refine h₁.trans (h₂.trans (Eventually.of_forall ?_))
  intro z
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,W,spectralPeterssonHilbertProfile]
  rw [← signed_packet_value N k negative v α m z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sourceJHolomorphicInfinityPacketL2_norm_sq_integral {ι : Type*}
    (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (hEven : Even k) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) :
    ‖sourceJHolomorphicInfinityPacketL2 N k hk hEven negative v α m‖^2 =
      ∫ z in gamma0InteriorRegion N, ‖gamma0PeterssonSourceInfinityPacket N k v
        (fun i => if negative then conj (α i) else α i) m z‖^2*z.im^k := by
  let P := sourceJHolomorphicInfinityPacketL2 N k hk hEven negative v α m
  let F := gamma0PeterssonSourceInfinityPacket N k v (fun i => if negative then conj (α i) else α i) m
  have h := sourceJHolomorphicInfinityPacketL2_coe N k hk hEven negative v α m
  have hF := (Lp.memLp P).ae_eq h
  have hP : P = hF.toLp (spectralPeterssonHilbertProfile k (spectralPeterssonSignVector negative F)) :=
    Lp.ext (h.trans hF.coeFn_toLp.symm)
  change ‖P‖^2 = ∫ z in gamma0InteriorRegion N, ‖F z‖^2*z.im^k
  rw [hP]
  simpa only [signed_vector_norm] using
    gamma0PeterssonHilbert_norm_sq_integral N k (spectralPeterssonSignVector negative F) hF

theorem sourceJHolomorphicAtkinL2_norm_sq_integral
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (negative : Bool) (n : ℕ+) :
    ‖gamma0PeterssonSourceAtkinL2 r s hcop hab k hk hEven negative n‖^2 =
      ∫ z in gamma0InteriorRegion (r*s), ‖gamma0PeterssonSourceAtkin r s hab k n z‖^2*z.im^k := by
  simpa only [gamma0PeterssonSourceAtkinL2,signed_vector_norm] using
    gamma0PeterssonHilbert_norm_sq_integral (r*s) k
      (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab k n))
      (gamma0PeterssonSourceAtkin_memLp r s hcop hab k hk hEven negative n)

end
end ArtinMatthews
