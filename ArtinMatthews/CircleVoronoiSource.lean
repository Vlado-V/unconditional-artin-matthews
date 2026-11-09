module

public import ArtinMatthews.CircleSourceDetector


set_option backward.privateInPublic true
@[expose] public section

/-! Exact passage between a finitely supported source and the infinite-sum
notation of double Voronoi. All circle and congruence sums are finite. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem circle_source_sum (H d m3 m4 : ℕ) [NeZero H] [NeZero d]
    (v3 v4 : (ZMod (H*d))ˣ)
    (hv3 : (v3 : ZMod (H*d))=(m3 : ZMod (H*d)))
    (hv4 : (v4 : ZMod (H*d))=(m4 : ZMod (H*d)))
    (S : Finset (ℕ×ℕ)) (A : ℕ×ℕ → ℂ) (hzero : ∀ k∉S, A k=0) :
    (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ∑' k : ℕ×ℕ,
      A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j))/(d : ℂ) =
      ∑ k∈S, A k*primitiveCircleSum (H*d) (circleShiftedFrequency m3 m4 k)*
        (if (d : ℤ)∣((k.1 : ℤ)-1) then 1 else 0) := by
  classical
  have hfinite (a : (ZMod (H*d))ˣ) (j : ZMod d) :
      (∑' k : ℕ×ℕ, A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j)) =
      ∑ k∈S, A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j) := by
    apply tsum_eq_sum
    intro k hk
    rw [hzero k hk,zero_mul]
  simp_rw [hfinite]
  have hswap : (∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d, ∑ k∈S,
      A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j)) =
      ∑ k∈S, A k*(∑ a : (ZMod (H*d))ˣ, ∑ j : ZMod d,
        ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j)) := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ a : (ZMod (H*d))ˣ, ∑ k∈S, ∑ j : ZMod d,
          A k*ZMod.stdAddChar (doubleVoronoiSourceDetector H d v3 v4 a k.1 k.2 j) := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_div_assoc,circle_source_detector H d m3 m4 v3 v4 hv3 hv4 k]
  ring

end ArtinMatthews
