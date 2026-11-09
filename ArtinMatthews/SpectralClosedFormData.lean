module

public import ArtinMatthews.SpectralClosedSubspaceResolvent


set_option backward.privateInPublic true
@[expose] public section

/-! Package the actual closed form data before specializing its resolvent.
The package keeps the inherited Hilbert structures fixed throughout the
proof and avoids reconstructing a nested subtype at each operator theorem. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

structure SpectralClosedFormData (V H : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  subspace : Submodule ℂ V
  closed : IsClosed (subspace:Set V)
  inclusion : V →L[ℂ] H
  compact : IsCompactOperator (spectralClosedFormInclusion subspace inclusion)
  injective : Function.Injective inclusion
  bound : ∀ u : subspace, ‖inclusion u.val‖≤‖u‖

namespace SpectralClosedFormData
section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def exceptional (d : SpectralClosedFormData V H) : Set ℂ :=
  spectralClosedFormExceptional d.subspace d.closed d.inclusion

def resolvent (d : SpectralClosedFormData V H) : ℂ → H →L[ℂ] H :=
  spectralClosedFormResolvent d.subspace d.closed d.inclusion

theorem exceptional_finite_norm_le (d : SpectralClosedFormData V H) (R : ℝ) (hR : 0≤R) :
    {z : ℂ | z∈d.exceptional ∧ ‖z‖≤R}.Finite :=
  spectralClosedFormExceptional_finite_norm_le d.subspace d.closed d.inclusion d.compact R hR

theorem exceptional_nonnegative (d : SpectralClosedFormData V H) (z : ℂ) (hz : z∈d.exceptional) :
    ∃ r : ℝ, 0≤r ∧ z=(r:ℂ) :=
  spectralClosedFormExceptional_nonnegative d.subspace d.closed d.inclusion d.injective d.bound z hz

theorem resolvent_meromorphic (d : SpectralClosedFormData V H) : Meromorphic d.resolvent :=
  spectralClosedFormResolvent_meromorphic d.subspace d.closed d.inclusion d.compact

theorem resolvent_weak (d : SpectralClosedFormData V H) (z : ℂ) (hz : z∉d.exceptional) (F : H) :
    ∃ u : V, u∈d.subspace ∧ d.inclusion u=d.resolvent z F ∧
      ∀ v : V, v∈d.subspace → inner ℂ v u-(z+1)*inner ℂ (d.inclusion v) (d.inclusion u)=
        inner ℂ (d.inclusion v) F := by
  let u := spectralClosedFormWeakResolvent d.subspace d.closed d.inclusion z F
  refine ⟨u.val,u.property,rfl,?_⟩
  intro v hv
  exact spectralClosedFormWeakResolvent_equation d.subspace d.closed d.inclusion d.compact z hz F ⟨v,hv⟩

end
end SpectralClosedFormData
end ArtinMatthews
