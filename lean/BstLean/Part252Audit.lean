import BstLean.Part252BaseEvent
import BstLean.Part252Centre
import BstLean.Part252CentreCharge
import BstLean.Part252CentreMeas
import BstLean.Part252CompletedRoot
import BstLean.Part252DirectionEvent
import BstLean.Part252Energy
import BstLean.Part252EnergyCap
import BstLean.Part252EnergyEvent
import BstLean.Part252EnergyRange
import BstLean.Part252FiniteCentre
import BstLean.Part252FluctNum
import BstLean.Part252FourTable
import BstLean.Part252GuardedTable
import BstLean.Part252HQPackage
import BstLean.Part252HQPacket
import BstLean.Part252HQRoot
import BstLean.Part252LatMomPacket
import BstLean.Part252LatitudeCap
import BstLean.Part252LatitudeMoments
import BstLean.Part252LatitudeVariance
import BstLean.Part252LowMass
import BstLean.Part252LowMassNum
import BstLean.Part252MatrixEvent
import BstLean.Part252MomentNum
import BstLean.Part252NodeMeasure
import BstLean.Part252NodeVariance
import BstLean.Part252NormalizedVariance
import BstLean.Part252Operator
import BstLean.Part252OperatorCap
import BstLean.Part252OperatorEvent
import BstLean.Part252PaidBase
import BstLean.Part252Pass
import BstLean.Part252PassEvent
import BstLean.Part252PositiveOutput
import BstLean.Part252ProductCharge
import BstLean.Part252RadiusPolynomial
import BstLean.Part252RetunedMass
import BstLean.Part252Root
import BstLean.Part252RootEvent
import BstLean.Part252Scalar
import BstLean.Part252ScaleMoment
import BstLean.Part252SharedPackage
import BstLean.Part252SplitNum
import BstLean.Part252Table
import BstLean.Part252TableBiasNum
import BstLean.Part252TableCoefficients
import BstLean.Part252TableEnvelope
import BstLean.Part252TableEvent
import BstLean.Part252TableFluctNum
import BstLean.Part252TableNum
import BstLean.Part252TablePayment
import BstLean.Part252TablePrices
import BstLean.Part252TableStatisticsNum
import BstLean.Part252TableSupply
import BstLean.Part252TableWorld
import BstLean.Part252Variance
import BstLean.Part252VarianceMoment

/-! Audit every explicit Part252 declaration. -/

#print axioms BstLean.Part252.worldAngles
#print axioms BstLean.Part252.worldAngles_measurable
#print axioms BstLean.Part252.worldAngles_charge
#print axioms BstLean.Part252.analyticBase
#print axioms BstLean.Part252.analyticCharge
#print axioms BstLean.Part252.tableChargeAllowance
#print axioms BstLean.Part252.analyticBase_measurable
#print axioms BstLean.Part252.analyticBase_charge
#print axioms BstLean.Part252.AnalyticBaseCertificate
#print axioms BstLean.Part252.analyticBaseCertificate
#print axioms BstLean.Part252.baseEvent
#print axioms BstLean.Part252.baseEvent_measurable
#print axioms BstLean.Part252.baseEvent_charge
#print axioms BstLean.Part252.BaseEventCertificate
#print axioms BstLean.Part252.baseEventCertificate
#print axioms BstLean.Part252.outputCentreEvent
#print axioms BstLean.Part252.outputCentreEvent_measurable
#print axioms BstLean.Part252.outputCentreEvent_charge
#print axioms BstLean.Part252.chi_row
#print axioms BstLean.Part252.outputCentre_row
#print axioms BstLean.Part252.exp_neg12_row
#print axioms BstLean.Part252.outputCentre_charge_row
#print axioms BstLean.Part252.centreSources_charge_row
#print axioms BstLean.Part252.centreSources_ret_charge_row
#print axioms BstLean.Part252.CentreSources
#print axioms BstLean.Part252.measurableSet_EnergySources
#print axioms BstLean.Part252.measurableSet_FullSources
#print axioms BstLean.Part252.measurableSet_CentreSources
#print axioms BstLean.Part252.rootWorldInterval
#print axioms BstLean.Part252.rootWorldInterval_cover
#print axioms BstLean.Part252.actual_world_interval
#print axioms BstLean.Part252.actual_world_window
#print axioms BstLean.Part252.completedRootInputs
#print axioms BstLean.Part252.CompletedRootCertificate
#print axioms BstLean.Part252.completedRootCertificate
#print axioms BstLean.Part252.completed_replacement
#print axioms BstLean.Part252.completedAgentPackage
#print axioms BstLean.Part252.measurable_standPoint_fam
#print axioms BstLean.Part252.measurable_inputErrorAverage_fam
#print axioms BstLean.Part252.DirectionError
#print axioms BstLean.Part252.measurableSet_DirectionError
#print axioms BstLean.Part252.directionError_ret_charge
#print axioms BstLean.Part252.latitude_integral_eq
#print axioms BstLean.Part252.energy_latitude_norm
#print axioms BstLean.Part252.location_sq_le_energy
#print axioms BstLean.Part252.full_location_moment
#print axioms BstLean.Part252.rotation16_le
#print axioms BstLean.Part252.energy_allowance_row
#print axioms BstLean.Part252.full_location_moment_row
#print axioms BstLean.Part252.Energy32
#print axioms BstLean.Part252.measurableSet_Energy32
#print axioms BstLean.Part252.energy32_ret_charge
#print axioms BstLean.Part252.kernel_lower_rational
#print axioms BstLean.Part252.energy_g_bounds
#print axioms BstLean.Part252.energy_g_root_guard
#print axioms BstLean.Part252.energy_ratio_coarse
#print axioms BstLean.Part252.energy_upper_coarse
#print axioms BstLean.Part252.energy_mean_lower_coarse
#print axioms BstLean.Part252.energy_lower_components
#print axioms BstLean.Part252.energy_lower_coarse
#print axioms BstLean.Part252.computed_energy_eq
#print axioms BstLean.Part252.centre_energy_range
#print axioms BstLean.Part252.wn_upper
#print axioms BstLean.Part252.cs_lower
#print axioms BstLean.Part252.deltaChi_upper
#print axioms BstLean.Part252.finite_centre_upper
#print axioms BstLean.Part252.FluctPriceBounds
#print axioms BstLean.Part252.fluct_chi_price
#print axioms BstLean.Part252.fluct_cubic_price
#print axioms BstLean.Part252.fluct_mixture_root
#print axioms BstLean.Part252.fourAllowances
#print axioms BstLean.Part252.actualFourError
#print axioms BstLean.Part252.actualFour_decomposition
#print axioms BstLean.Part252.FourTableMoments
#print axioms BstLean.Part252.fourTableMoments_to_event
#print axioms BstLean.Part252.guardedTableAllowance
#print axioms BstLean.Part252.guarded_table_allocation
#print axioms BstLean.Part252.guarded_table_allowance_exact
#print axioms BstLean.Part252.guarded_table_slack
#print axioms BstLean.Part252.GuardedTablePayment
#print axioms BstLean.Part252.guardedTablePayment_of_tablePayment
#print axioms BstLean.Part252.hqBaseEvent_charge_of_guarded
#print axioms BstLean.Part252.hqBaseEvent
#print axioms BstLean.Part252.hqBaseEvent_measurable
#print axioms BstLean.Part252.hqBaseEvent_charge
#print axioms BstLean.Part252.hqRootInputs_on_base
#print axioms BstLean.Part252.hqAgentPackage_of_base_charge
#print axioms BstLean.Part252.hqAgentPackage
#print axioms BstLean.Part252.hqEnergy
#print axioms BstLean.Part252.hqDisplacement
#print axioms BstLean.Part252.hqEnergyMoment
#print axioms BstLean.Part252.hqLocationMoment
#print axioms BstLean.Part252.hq_price_certificate
#print axioms BstLean.Part252.splitRemovedBudget
#print axioms BstLean.Part252.splitRemovedBudget_bounds
#print axioms BstLean.Part252.hq_displacement_root
#print axioms BstLean.Part252.hq_root_price
#print axioms BstLean.Part252.LowResidualMass
#print axioms BstLean.Part252.hqSplit
#print axioms BstLean.Part252.hq_output_bounds
#print axioms BstLean.Part252.hq_fluctuation
#print axioms BstLean.Part252.hq_passes
#print axioms BstLean.Part252.hqRootInputs
#print axioms BstLean.Part252.locationVarianceBudget
#print axioms BstLean.Part252.residualVarianceBudget
#print axioms BstLean.Part252.location_variance_on_event
#print axioms BstLean.Part252.residual_variance_on_event
#print axioms BstLean.Part252.latitudeMoments
#print axioms BstLean.Part252.root_le_of_pow
#print axioms BstLean.Part252.gaussian80_le
#print axioms BstLean.Part252.exact_radius_sq_row
#print axioms BstLean.Part252.plane_envelope_row
#print axioms BstLean.Part252.plane_squared_row
#print axioms BstLean.Part252.operator_envelope_row
#print axioms BstLean.Part252.jacobian_squared_row
#print axioms BstLean.Part252.latitude_constant_sharp_row
#print axioms BstLean.Part252.latitude_constant_row
#print axioms BstLean.Part252.latitudeC
#print axioms BstLean.Part252.locationMomentBudget
#print axioms BstLean.Part252.residualMomentBudget
#print axioms BstLean.Part252.rotation_positive
#print axioms BstLean.Part252.locationMomentBudget_pos
#print axioms BstLean.Part252.residualMomentBudget_pos
#print axioms BstLean.Part252.location_moment_on_event
#print axioms BstLean.Part252.residual_moment_on_event
#print axioms BstLean.Part252.splitLocationWidth
#print axioms BstLean.Part252.splitResidualWidth
#print axioms BstLean.Part252.lowMassBudget
#print axioms BstLean.Part252.removal_of_low_mass
#print axioms BstLean.Part252.latitudeVariance
#print axioms BstLean.Part252.measurable_latitudeVariance
#print axioms BstLean.Part252.latitudeVariance_nonneg
#print axioms BstLean.Part252.latitude_variance_norm12
#print axioms BstLean.Part252.conditionalVariance_scale
#print axioms BstLean.Part252.lambda_variance_norm12
#print axioms BstLean.Part252.residual_variance_norm12
#print axioms BstLean.Part252.latitude_mass_of_MASS
#print axioms BstLean.Part252.low_mass_of_interfaces
#print axioms BstLean.Part252.rotation_sixteen_sharp
#print axioms BstLean.Part252.energy_allowance_sharp_row
#print axioms BstLean.Part252.low_mass_gap
#print axioms BstLean.Part252.low_mass_price_row
#print axioms BstLean.Part252.low_mass_of_three_bounds
#print axioms BstLean.Part252.FirstMatrix
#print axioms BstLean.Part252.firstMatrix_measurable
#print axioms BstLean.Part252.firstMatrix_charge
#print axioms BstLean.Part252.first_matrix_row
#print axioms BstLean.Part252.second_matrix_row
#print axioms BstLean.Part252.variance_of_matrix_events
#print axioms BstLean.Part252.rotation_rational_bound
#print axioms BstLean.Part252.rotation_four
#print axioms BstLean.Part252.rotation_six
#print axioms BstLean.Part252.rotation_twelve
#print axioms BstLean.Part252.location_budget_cap
#print axioms BstLean.Part252.residual_budget_cap
#print axioms BstLean.Part252.location_budgets_row
#print axioms BstLean.Part252.residual_budgets_row
#print axioms BstLean.Part252.variance_budgets_row
#print axioms BstLean.Part252.full_residual_budget_row
#print axioms BstLean.Part252.scale_variance_budget_row
#print axioms BstLean.Part252.tableNodeIndex
#print axioms BstLean.Part252.tableNodeIndex_measurable
#print axioms BstLean.Part252.tableNodeMeasure
#print axioms BstLean.Part252.tableNodeMeasure_mass
#print axioms BstLean.Part252.actualFour_node_lintegral
#print axioms BstLean.Part252.fourTableMoments_of_nodeMoments
#print axioms BstLean.Part252.tableEvent_of_nodeMoments
#print axioms BstLean.Part252.tableEvent_of_second_layer_good
#print axioms BstLean.Part252.table_second_layer_charge
#print axioms BstLean.Part252.table_second_layer_bad_subset
#print axioms BstLean.Part252.variance_alg_low
#print axioms BstLean.Part252.variance_alg_up
#print axioms BstLean.Part252.variance_alg_trace
#print axioms BstLean.Part252.variance_cheby_num
#print axioms BstLean.Part252.node_trace_charge
#print axioms BstLean.Part252.row_node_geometry
#print axioms BstLean.Part252.node_trace_charge_row
#print axioms BstLean.Part252.fLatitude_variance_norm12
#print axioms BstLean.Part252.zLatitude_variance_norm12
#print axioms BstLean.Part252.varianceTwelve
#print axioms BstLean.Part252.LatitudeVarianceCertificate
#print axioms BstLean.Part252.latitudeVarianceCertificate
#print axioms BstLean.Part252.fourth_on_operator_event
#print axioms BstLean.Part252.fourth_of_operator_cap
#print axioms BstLean.Part252.operatorCoefficient
#print axioms BstLean.Part252.operatorCoefficient_eq
#print axioms BstLean.Part252.operatorCoefficient_power
#print axioms BstLean.Part252.operator_cap
#print axioms BstLean.Part252.fourth_on_operator_event_8192
#print axioms BstLean.Part252.Operator160
#print axioms BstLean.Part252.measurableSet_Operator160
#print axioms BstLean.Part252.operator160_ret_charge
#print axioms BstLean.Part252.operator160_ret_moment
#print axioms BstLean.Part252.sharedGood
#print axioms BstLean.Part252.sharedGood_measurable
#print axioms BstLean.Part252.sharedGood_charge
#print axioms BstLean.Part252.sharedGood_subset
#print axioms BstLean.Part252.SharedEventCertificate
#print axioms BstLean.Part252.sharedEventCertificate
#print axioms BstLean.Part252.paidBaseEvent
#print axioms BstLean.Part252.paidBaseEvent_measurable
#print axioms BstLean.Part252.paidBaseEvent_charge
#print axioms BstLean.Part252.PaidBaseCertificate
#print axioms BstLean.Part252.paidBaseCertificate
#print axioms BstLean.Part252.paper_scale_lower
#print axioms BstLean.Part252.PaperMoments
#print axioms BstLean.Part252.passInputs_of_paperMoments
#print axioms BstLean.Part252.passEvent
#print axioms BstLean.Part252.passEvent_measurable
#print axioms BstLean.Part252.first_matrix_charge_row
#print axioms BstLean.Part252.second_matrix_charge_row
#print axioms BstLean.Part252.passEvent_charge
#print axioms BstLean.Part252.window_winC
#print axioms BstLean.Part252.fresh_latitude_constant_pos_row
#print axioms BstLean.Part252.pass_moments_of_events
#print axioms BstLean.Part252.pass_centre_of_events
#print axioms BstLean.Part252.positiveOutputEvent
#print axioms BstLean.Part252.positiveOutputEvent_measurable
#print axioms BstLean.Part252.positiveOutputEvent_charge
#print axioms BstLean.Part252.product_charge_ae
#print axioms BstLean.Part252.radius_square_moment_price
#print axioms BstLean.Part252.radius_polynomial_root_price
#print axioms BstLean.Part252.retuned_energy_cap
#print axioms BstLean.Part252.retuned_low_mass_gap
#print axioms BstLean.Part252.retuned_low_mass_price
#print axioms BstLean.Part252.sourceEvents_on_common
#print axioms BstLean.Part252.low_mass_on_cell
#print axioms BstLean.Part252.low_mass_on_common
#print axioms BstLean.Part252.rootInputs_on_common
#print axioms BstLean.Part252.replacement_on_common
#print axioms BstLean.Part252.retunedAgentPackage
#print axioms BstLean.Part252.retunedAgentPackage_of_guarded
#print axioms BstLean.Part252.rowSplit
#print axioms BstLean.Part252.row_split_floor
#print axioms BstLean.Part252.RootSource
#print axioms BstLean.Part252.row_pass_inputs
#print axioms BstLean.Part252.rootInputs
#print axioms BstLean.Part252.replacement_of_source
#print axioms BstLean.Part252.RootRemainder
#print axioms BstLean.Part252.rootSource_of_events
#print axioms BstLean.Part252.rootInputs_of_events
#print axioms BstLean.Part252.eta
#print axioms BstLean.Part252.mixtureFloor
#print axioms BstLean.Part252.biasFloor
#print axioms BstLean.Part252.chi
#print axioms BstLean.Part252.epsilon
#print axioms BstLean.Part252.varianceMax
#print axioms BstLean.Part252.energyError
#print axioms BstLean.Part252.locationError
#print axioms BstLean.Part252.locationNorm
#print axioms BstLean.Part252.varianceNorm
#print axioms BstLean.Part252.removalBudget
#print axioms BstLean.Part252.mixtureRoot
#print axioms BstLean.Part252.displacementBudget
#print axioms BstLean.Part252.biasRootCap
#print axioms BstLean.Part252.eta_pos
#print axioms BstLean.Part252.eta_lt_one
#print axioms BstLean.Part252.bias_floor_ge
#print axioms BstLean.Part252.bias_threshold_pos
#print axioms BstLean.Part252.stored_squared_price
#print axioms BstLean.Part252.stored_bias_root
#print axioms BstLean.Part252.removal_root
#print axioms BstLean.Part252.displacement_root
#print axioms BstLean.Part252.root_reserve
#print axioms BstLean.Part252.ScalarCertificate
#print axioms BstLean.Part252.scalarCertificate
#print axioms BstLean.Part252.fullResidualBudget
#print axioms BstLean.Part252.residual_sq_le_energy
#print axioms BstLean.Part252.full_residual_eighth
#print axioms BstLean.Part252.scaleVarianceBudget
#print axioms BstLean.Part252.scale_variance_on_event
#print axioms BstLean.Part252.window_of_theta
#print axioms BstLean.Part252.window_of_frame
#print axioms BstLean.Part252.energy_pos_of_frame
#print axioms BstLean.Part252.commonEvent
#print axioms BstLean.Part252.commonEvent_measurable
#print axioms BstLean.Part252.commonEvent_charge
#print axioms BstLean.Part252.sharedAgentPackage
#print axioms BstLean.Part252.rowSigma
#print axioms BstLean.Part252.hqCentreCap
#print axioms BstLean.Part252.hqEpsilon
#print axioms BstLean.Part252.hqKappa
#print axioms BstLean.Part252.hqLocation
#print axioms BstLean.Part252.hqExp
#print axioms BstLean.Part252.sigma_bounds
#print axioms BstLean.Part252.sigma_pos
#print axioms BstLean.Part252.split_width_bounds
#print axioms BstLean.Part252.residual_width_bounds
#print axioms BstLean.Part252.width_ratio_bounds
#print axioms BstLean.Part252.hq_epsilon_bounds
#print axioms BstLean.Part252.hq_kappa_bounds
#print axioms BstLean.Part252.hq_location_bounds
#print axioms BstLean.Part252.hq_exponential_bounds
#print axioms BstLean.Part252.inverse_eta_bound
#print axioms BstLean.Part252.iota_bounds
#print axioms BstLean.Part252.c2_eta_bounds
#print axioms BstLean.Part252.c3_eta_bounds
#print axioms BstLean.Part252.cE_width_bounds
#print axioms BstLean.Part252.cV_width_bounds
#print axioms BstLean.Part252.grid_f_bulk
#print axioms BstLean.Part252.grid_w_bulk
#print axioms BstLean.Part252.location_error_of_exact
#print axioms BstLean.Part252.energy_error_of_exact
#print axioms BstLean.Part252.table_coefficient_nonneg
#print axioms BstLean.Part252.table_location_correction
#print axioms BstLean.Part252.table_energy_correction
#print axioms BstLean.Part252.table_bias_prices
#print axioms BstLean.Part252.table_bias_charge_caps
#print axioms BstLean.Part252.TableCoefficientCertificate
#print axioms BstLean.Part252.table_coefficient_certificate
#print axioms BstLean.Part252.tableEnvelope
#print axioms BstLean.Part252.table_envelope_gap
#print axioms BstLean.Part252.table_envelope_D
#print axioms BstLean.Part252.table_envelope_V
#print axioms BstLean.Part252.table_envelope_P
#print axioms BstLean.Part252.tableEvent
#print axioms BstLean.Part252.tableEvent_measurable
#print axioms BstLean.Part252.exactTableMoments_of_event
#print axioms BstLean.Part252.proposedBaseEvent
#print axioms BstLean.Part252.proposedBaseEvent_measurable
#print axioms BstLean.Part252.TablePayment
#print axioms BstLean.Part252.proposedBaseEvent_charge
#print axioms BstLean.Part252.proposedBaseEvent_certificate
#print axioms BstLean.Part252.table_location_fluctuation_price
#print axioms BstLean.Part252.table_energy_coefficient
#print axioms BstLean.Part252.table_energy_fluctuation_price
#print axioms BstLean.Part252.table_remaining_price_allocation
#print axioms BstLean.Part252.row_sqrt_bounds
#print axioms BstLean.Part252.row_rule_size
#print axioms BstLean.Part252.row_bulk_radius
#print axioms BstLean.Part252.row_bulk_positive
#print axioms BstLean.Part252.row_grid_width
#print axioms BstLean.Part252.row_location_grid
#print axioms BstLean.Part252.row_energy_grid
#print axioms BstLean.Part252.row_location_rule
#print axioms BstLean.Part252.row_energy_rule
#print axioms BstLean.Part252.tablePairEvent
#print axioms BstLean.Part252.tablePairEvent_measurable
#print axioms BstLean.Part252.tableEvent_ret_charge
#print axioms BstLean.Part252.certifiedTablePayment
#print axioms BstLean.Part252.certifiedBaseEvent
#print axioms BstLean.Part252.certified_hq_base_charge
#print axioms BstLean.Part252.tableMomentPrices
#print axioms BstLean.Part252.table_statistics_nonneg
#print axioms BstLean.Part252.table_four_price
#print axioms BstLean.Part252.table_first_charge_price
#print axioms BstLean.Part252.table_total_charge_price
#print axioms BstLean.Part252.table_charge_price
#print axioms BstLean.Part252.table_gaussian_constant
#print axioms BstLean.Part252.table_radius_constant
#print axioms BstLean.Part252.table_statistics_constant
#print axioms BstLean.Part252.first_matrix_op_row
#print axioms BstLean.Part252.row_node_variance
#print axioms BstLean.Part252.ExactTableMoments
#print axioms BstLean.Part252.stored_table_moments
#print axioms BstLean.Part252.tableVarianceEvent
#print axioms BstLean.Part252.tableVarianceEvent_measurable
#print axioms BstLean.Part252.tableVarianceEvent_charge
#print axioms BstLean.Part252.tableFirstEvent
#print axioms BstLean.Part252.tableFirstEvent_measurable
#print axioms BstLean.Part252.tableFirstEvent_charge
#print axioms BstLean.Part252.tableBadPair
#print axioms BstLean.Part252.tableBadPair_measurable
#print axioms BstLean.Part252.table_conditional_charge
#print axioms BstLean.Part252.table_world_charge
#print axioms BstLean.Part252.variance_pointwise
#print axioms BstLean.Part252.variance_pointwise_row
#print axioms BstLean.Part252.variance_moment_of_latitude
#print axioms BstLean.Part252.variance_moment_row
