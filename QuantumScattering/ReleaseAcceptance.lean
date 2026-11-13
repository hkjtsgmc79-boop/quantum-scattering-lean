/- F2: one release endpoint, including the genuinely connected legacy bridge.
No public completion is inferred merely from the presence of this proof body.
The complete build, axiom checks and semantic review remain mandatory. -/
import QuantumScattering.FrameworkCompletion
import QuantumScattering.RectangularBridge

noncomputable section
namespace QuantumScattering

structure FrameworkReleaseCertificate : Prop where
  finite_layers : ∀ p:PhysicalProblem, ReusableFrameworkCertificate p
  legacy_wave : ∀ (p:QuantumTunneling.RectangularParameters) (a b:ℂ),
    RectangularBridge.rawWave p a b=p.coherentWave a b
  legacy_matrix : ∀ p:QuantumTunneling.RectangularParameters,
    (RectangularBridge.model p).problem.channels.scatteringMatrix=p.layer.scatteringMatrix
  coherent_cascade : ∀ M N:ChannelTransfer,
    M.feedback N≠0 ∧ (N.after M).t=N.t*M.t/M.feedback N ∧
    (N.after M).rLeft=M.rLeft+M.t^2*N.rLeft/M.feedback N ∧
    (N.after M).rRight=N.rRight+N.t^2*M.rRight/M.feedback N
  exact_refinement : ∀ (l r:Port) (pre post:Stack) (δ a b:ℝ) (ha:0<a) (hb:0<b),
    (channelTransfer l r (Stack.transfer
      (pre++[Layer.segment δ (a+b) (add_pos ha hb)]++post))).scatteringMatrix=
    (channelTransfer l r (Stack.transfer
      (pre++[Layer.segment δ a ha,Layer.segment δ b hb]++post))).scatteringMatrix
  backend_differential_contract : ∀ s:EvolutionSegment, ∀ iL iR:ℂ,
    ∃! fv:(ℝ→ℂ)×(ℝ→ℂ), s.Admissible iL iR fv.1 fv.2
  nonconstant_backend_witness :
    SmoothBackend.evolution.coefficient 0≠SmoothBackend.evolution.coefficient 1

/-- The full source-level acceptance target. No unproved mathematical fields
are supplied by callers; every field is constructed from the preceding chain. -/
theorem reusable_scattering_framework_release : FrameworkReleaseCertificate where
  finite_layers := reusable_finite_layer_framework
  legacy_wave := RectangularBridge.wave_eq_legacy
  legacy_matrix := RectangularBridge.scatteringMatrix_eq_legacy
  coherent_cascade := fun M N => ⟨M.feedback_ne_zero N,M.cascade_transmission N,
    M.cascade_reflection_left N,M.cascade_reflection_right N⟩
  exact_refinement := Stack.split_scattering
  backend_differential_contract := EvolutionSegment.existsUnique_scattering
  nonconstant_backend_witness := SmoothBackend.coefficient_not_constant

end QuantumScattering
