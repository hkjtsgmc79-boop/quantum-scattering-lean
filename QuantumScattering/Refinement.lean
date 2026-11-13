/- F2: inserting an artificial interface inside a constant medium does not
change physical scattering. This is exact refinement, NOT convergence of
piecewise approximations to an arbitrary potential. Uncompiled candidates. -/
import QuantumScattering.FlowComposition
import QuantumScattering.TransferComposition

noncomputable section
namespace QuantumScattering
namespace Layer

def segment (δ a : ℝ) (ha : 0<a) : Layer := ⟨δ,a,ha⟩

lemma split_transfer (δ a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (segment δ (a+b) (add_pos ha hb)).transfer=
      (segment δ b hb).transfer.after (segment δ a ha).transfer := by
  exact (LocalProfile.ofDelta δ).transfer_add a b
end Layer
namespace Stack

lemma split_transfer (pre post : Stack) (δ a b : ℝ) (ha : 0<a) (hb : 0<b) :
    transfer (pre++[Layer.segment δ (a+b) (add_pos ha hb)]++post)=
      transfer (pre++[Layer.segment δ a ha,Layer.segment δ b hb]++post) := by
  simp only [transfer_append,transfer,RealTransfer.identity_after]
  rw [Layer.split_transfer]

lemma split_width (pre post : Stack) (δ a b : ℝ) (ha : 0<a) (hb : 0<b) :
    width (pre++[Layer.segment δ (a+b) (add_pos ha hb)]++post)=
      width (pre++[Layer.segment δ a ha,Layer.segment δ b hb]++post) := by
  simp [width_append,width,Layer.segment,add_assoc]

/-- All exterior amplitudes, including phases, are unchanged by subdivision. -/
theorem split_scattering (l r : Port) (pre post : Stack) (δ a b : ℝ)
    (ha : 0<a) (hb : 0<b) :
    (channelTransfer l r
      (transfer (pre++[Layer.segment δ (a+b) (add_pos ha hb)]++post))).scatteringMatrix=
    (channelTransfer l r
      (transfer (pre++[Layer.segment δ a ha,Layer.segment δ b hb]++post))).scatteringMatrix := by
  rw [split_transfer]

/-- The actual interior and exterior state agrees too, for a split first layer. -/
lemma split_tail (r : Port) (post : Stack) (δ a b : ℝ)
    (ha : 0<a) (hb : 0<b) (y : State) (x : ℝ) :
    tail r (Layer.segment δ (a+b) (add_pos ha hb)::post) y x=
      tail r (Layer.segment δ a ha::Layer.segment δ b hb::post) y x := by
  let P := LocalProfile.ofDelta δ
  have htransfer := Layer.split_transfer δ a b ha hb
  by_cases hxa : x<a
  · have hxab : x<a+b := by linarith
    simp [tail,Layer.segment,hxa,hxab,Layer.flow,Layer.profile]
  · by_cases hxab : x<a+b
    · have hxmb : x-a<b := by linarith
      simp [tail, Layer.segment, hxa, hxab, hxmb]
      change P.flow y x=P.flow (P.flow y a) (x-a)
      simpa using P.flow_add y a (x-a)
    · have hxmb : ¬x-a<b := by linarith
      simp [tail, Layer.segment, hxa, hxab, hxmb]
      have hT : (P.transfer (a+b)).act y=(P.transfer b).act ((P.transfer a).act y) := by
        rw [P.transfer_add,RealTransfer.after_act]
      change tail r post ((P.transfer (a+b)).act y) (x-(a+b))=
        tail r post ((P.transfer b).act ((P.transfer a).act y)) (x-a-b)
      rw [hT]
      congr 1
      ring

lemma split_tail_anywhere (r : Port) (pre post : Stack) (δ a b : ℝ)
    (ha : 0<a) (hb : 0<b) (y : State) (x : ℝ) :
    tail r (pre++Layer.segment δ (a+b) (add_pos ha hb)::post) y x=
      tail r (pre++Layer.segment δ a ha::Layer.segment δ b hb::post) y x := by
  induction pre generalizing y x with
  | nil => exact split_tail r post δ a b ha hb y x
  | cons s rest ih =>
    by_cases hx : x<s.width
    · simp [tail,hx]
    · simp only [List.cons_append,tail,if_neg hx]
      exact ih (s.transfer.act y) (x-s.width)

end Stack
end QuantumScattering
