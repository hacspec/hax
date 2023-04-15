type error_flag = CFatal | CAlwaysError | CError | CWarning | CSilent
val uu___is_CFatal : error_flag -> Prims.bool
val uu___is_CAlwaysError : error_flag -> Prims.bool
val uu___is_CError : error_flag -> Prims.bool
val uu___is_CWarning : error_flag -> Prims.bool
val uu___is_CSilent : error_flag -> Prims.bool
type raw_error =
    Error_DependencyAnalysisFailed
  | Error_IDETooManyPops
  | Error_IDEUnrecognized
  | Error_InductiveTypeNotSatisfyPositivityCondition
  | Error_InvalidUniverseVar
  | Error_MissingFileName
  | Error_ModuleFileNameMismatch
  | Error_OpPlusInUniverse
  | Error_OutOfRange
  | Error_ProofObligationFailed
  | Error_TooManyFiles
  | Error_TypeCheckerFailToProve
  | Error_TypeError
  | Error_UncontrainedUnificationVar
  | Error_UnexpectedGTotComputation
  | Error_UnexpectedInstance
  | Error_UnknownFatal_AssertionFailure
  | Error_Z3InvocationError
  | Error_IDEAssertionFailure
  | Error_Z3SolverError
  | Fatal_AbstractTypeDeclarationInInterface
  | Fatal_ActionMustHaveFunctionType
  | Fatal_AlreadyDefinedTopLevelDeclaration
  | Fatal_ArgumentLengthMismatch
  | Fatal_AssertionFailure
  | Fatal_AssignToImmutableValues
  | Fatal_AssumeValInInterface
  | Fatal_BadlyInstantiatedSynthByTactic
  | Fatal_BadSignatureShape
  | Fatal_BinderAndArgsLengthMismatch
  | Fatal_BothValAndLetInInterface
  | Fatal_CardinalityConstraintViolated
  | Fatal_ComputationNotTotal
  | Fatal_ComputationTypeNotAllowed
  | Fatal_ComputedTypeNotMatchAnnotation
  | Fatal_ConstructorArgLengthMismatch
  | Fatal_ConstructorFailedCheck
  | Fatal_ConstructorNotFound
  | Fatal_ConstsructorBuildWrongType
  | Fatal_CycleInRecTypeAbbreviation
  | Fatal_DataContructorNotFound
  | Fatal_DefaultQualifierNotAllowedOnEffects
  | Fatal_DefinitionNotFound
  | Fatal_DisjuctivePatternVarsMismatch
  | Fatal_DivergentComputationCannotBeIncludedInTotal
  | Fatal_DuplicateInImplementation
  | Fatal_DuplicateModuleOrInterface
  | Fatal_DuplicateTopLevelNames
  | Fatal_DuplicateTypeAnnotationAndValDecl
  | Fatal_EffectCannotBeReified
  | Fatal_EffectConstructorNotFullyApplied
  | Fatal_EffectfulAndPureComputationMismatch
  | Fatal_EffectNotFound
  | Fatal_EffectsCannotBeComposed
  | Fatal_ErrorInSolveDeferredConstraints
  | Fatal_ErrorsReported
  | Fatal_EscapedBoundVar
  | Fatal_ExpectedArrowAnnotatedType
  | Fatal_ExpectedGhostExpression
  | Fatal_ExpectedPureExpression
  | Fatal_ExpectNormalizedEffect
  | Fatal_ExpectTermGotFunction
  | Fatal_ExpectTrivialPreCondition
  | Fatal_FailToCompileNativeTactic
  | Fatal_FailToExtractNativeTactic
  | Fatal_FailToProcessPragma
  | Fatal_FailToResolveImplicitArgument
  | Fatal_FailToSolveUniverseInEquality
  | Fatal_FieldsNotBelongToSameRecordType
  | Fatal_ForbiddenReferenceToCurrentModule
  | Fatal_FreeVariables
  | Fatal_FunctionTypeExpected
  | Fatal_IdentifierNotFound
  | Fatal_IllAppliedConstant
  | Fatal_IllegalCharInByteArray
  | Fatal_IllegalCharInOperatorName
  | Fatal_IllTyped
  | Fatal_ImpossibleAbbrevLidBundle
  | Fatal_ImpossibleAbbrevRenameBundle
  | Fatal_ImpossibleInductiveWithAbbrev
  | Fatal_ImpossiblePrePostAbs
  | Fatal_ImpossiblePrePostArrow
  | Fatal_ImpossibleToGenerateDMEffect
  | Fatal_ImpossibleTypeAbbrevBundle
  | Fatal_ImpossibleTypeAbbrevSigeltBundle
  | Fatal_IncludeModuleNotPrepared
  | Fatal_IncoherentInlineUniverse
  | Fatal_IncompatibleKinds
  | Fatal_IncompatibleNumberOfTypes
  | Fatal_IncompatibleSetOfUniverse
  | Fatal_IncompatibleUniverse
  | Fatal_InconsistentImplicitArgumentAnnotation
  | Fatal_InconsistentImplicitQualifier
  | Fatal_InconsistentQualifierAnnotation
  | Fatal_InferredTypeCauseVarEscape
  | Fatal_InlineRenamedAsUnfold
  | Fatal_InsufficientPatternArguments
  | Fatal_InterfaceAlreadyProcessed
  | Fatal_InterfaceNotImplementedByModule
  | Fatal_InterfaceWithTypeImplementation
  | Fatal_InvalidFloatingPointNumber
  | Fatal_InvalidFSDocKeyword
  | Fatal_InvalidIdentifier
  | Fatal_InvalidLemmaArgument
  | Fatal_InvalidNumericLiteral
  | Fatal_InvalidRedefinitionOfLexT
  | Fatal_InvalidUnicodeInStringLiteral
  | Fatal_InvalidUTF8Encoding
  | Fatal_InvalidWarnErrorSetting
  | Fatal_LetBoundMonadicMismatch
  | Fatal_LetMutableForVariablesOnly
  | Fatal_LetOpenModuleOnly
  | Fatal_LetRecArgumentMismatch
  | Fatal_MalformedActionDeclaration
  | Fatal_MismatchedPatternType
  | Fatal_MismatchUniversePolymorphic
  | Fatal_MissingDataConstructor
  | Fatal_MissingExposeInterfacesOption
  | Fatal_MissingFieldInRecord
  | Fatal_MissingImplementation
  | Fatal_MissingImplicitArguments
  | Fatal_MissingInterface
  | Fatal_MissingNameInBinder
  | Fatal_MissingPrimsModule
  | Fatal_MissingQuantifierBinder
  | Fatal_ModuleExpected
  | Fatal_ModuleFileNotFound
  | Fatal_ModuleFirstStatement
  | Fatal_ModuleNotFound
  | Fatal_ModuleOrFileNotFound
  | Fatal_MonadAlreadyDefined
  | Fatal_MoreThanOneDeclaration
  | Fatal_MultipleLetBinding
  | Fatal_NameNotFound
  | Fatal_NameSpaceNotFound
  | Fatal_NegativeUniverseConstFatal_NotSupported
  | Fatal_NoFileProvided
  | Fatal_NonInductiveInMutuallyDefinedType
  | Fatal_NonLinearPatternNotPermitted
  | Fatal_NonLinearPatternVars
  | Fatal_NonSingletonTopLevel
  | Fatal_NonSingletonTopLevelModule
  | Error_NonTopRecFunctionNotFullyEncoded
  | Fatal_NonTrivialPreConditionInPrims
  | Fatal_NonVariableInductiveTypeParameter
  | Fatal_NotApplicationOrFv
  | Fatal_NotEnoughArgsToEffect
  | Fatal_NotEnoughArgumentsForEffect
  | Fatal_NotFunctionType
  | Fatal_NotSupported
  | Fatal_NotTopLevelModule
  | Fatal_NotValidFStarFile
  | Fatal_NotValidIncludeDirectory
  | Fatal_OneModulePerFile
  | Fatal_OpenGoalsInSynthesis
  | Fatal_OptionsNotCompatible
  | Fatal_OutOfOrder
  | Fatal_ParseErrors
  | Fatal_ParseItError
  | Fatal_PolyTypeExpected
  | Fatal_PossibleInfiniteTyp
  | Fatal_PreModuleMismatch
  | Fatal_QulifierListNotPermitted
  | Fatal_RecursiveFunctionLiteral
  | Fatal_ReflectOnlySupportedOnEffects
  | Fatal_ReservedPrefix
  | Fatal_SMTOutputParseError
  | Fatal_SMTSolverError
  | Fatal_SyntaxError
  | Fatal_SynthByTacticError
  | Fatal_TacticGotStuck
  | Fatal_TcOneFragmentFailed
  | Fatal_TermOutsideOfDefLanguage
  | Fatal_ToManyArgumentToFunction
  | Fatal_TooManyOrTooFewFileMatch
  | Fatal_TooManyPatternArguments
  | Fatal_TooManyUniverse
  | Fatal_TypeMismatch
  | Fatal_TypeWithinPatternsAllowedOnVariablesOnly
  | Fatal_UnableToReadFile
  | Fatal_UnepxectedOrUnboundOperator
  | Fatal_UnexpectedBinder
  | Fatal_UnexpectedBindShape
  | Fatal_UnexpectedChar
  | Fatal_UnexpectedComputationTypeForLetRec
  | Fatal_UnexpectedConstructorType
  | Fatal_UnexpectedDataConstructor
  | Fatal_UnexpectedEffect
  | Fatal_UnexpectedEmptyRecord
  | Fatal_UnexpectedExpressionType
  | Fatal_UnexpectedFunctionParameterType
  | Fatal_UnexpectedGeneralizedUniverse
  | Fatal_UnexpectedGTotForLetRec
  | Fatal_UnexpectedGuard
  | Fatal_UnexpectedIdentifier
  | Fatal_UnexpectedImplicitArgument
  | Fatal_UnexpectedImplictArgument
  | Fatal_UnexpectedInductivetype
  | Fatal_UnexpectedLetBinding
  | Fatal_UnexpectedModuleDeclaration
  | Fatal_UnexpectedNumberOfUniverse
  | Fatal_UnexpectedNumericLiteral
  | Fatal_UnexpectedPattern
  | Fatal_UnexpectedPosition
  | Fatal_UnExpectedPreCondition
  | Fatal_UnexpectedReturnShape
  | Fatal_UnexpectedSignatureForMonad
  | Fatal_UnexpectedTerm
  | Fatal_UnexpectedTermInUniverse
  | Fatal_UnexpectedTermType
  | Fatal_UnexpectedTermVQuote
  | Fatal_UnexpectedUniversePolymorphicReturn
  | Fatal_UnexpectedUniverseVariable
  | Fatal_UnfoldableDeprecated
  | Fatal_UnificationNotWellFormed
  | Fatal_Uninstantiated
  | Error_UninstantiatedUnificationVarInTactic
  | Fatal_UninstantiatedVarInTactic
  | Fatal_UniverseMightContainSumOfTwoUnivVars
  | Fatal_UniversePolymorphicInnerLetBound
  | Fatal_UnknownAttribute
  | Fatal_UnknownToolForDep
  | Fatal_UnrecognizedExtension
  | Fatal_UnresolvedPatternVar
  | Fatal_UnsupportedConstant
  | Fatal_UnsupportedDisjuctivePatterns
  | Fatal_UnsupportedQualifier
  | Fatal_UserTacticFailure
  | Fatal_ValueRestriction
  | Fatal_VariableNotFound
  | Fatal_WrongBodyTypeForReturnWP
  | Fatal_WrongDataAppHeadFormat
  | Fatal_WrongDefinitionOrder
  | Fatal_WrongResultTypeAfterConstrutor
  | Fatal_WrongTerm
  | Fatal_WhenClauseNotSupported
  | Unused01
  | Warning_AddImplicitAssumeNewQualifier
  | Warning_AdmitWithoutDefinition
  | Warning_CachedFile
  | Warning_DefinitionNotTranslated
  | Warning_DependencyFound
  | Warning_DeprecatedEqualityOnBinder
  | Warning_DeprecatedOpaqueQualifier
  | Warning_DocOverwrite
  | Warning_FileNotWritten
  | Warning_Filtered
  | Warning_FunctionLiteralPrecisionLoss
  | Warning_FunctionNotExtacted
  | Warning_HintFailedToReplayProof
  | Warning_HitReplayFailed
  | Warning_IDEIgnoreCodeGen
  | Warning_IllFormedGoal
  | Warning_InaccessibleArgument
  | Warning_IncoherentImplicitQualifier
  | Warning_IrrelevantQualifierOnArgumentToReflect
  | Warning_IrrelevantQualifierOnArgumentToReify
  | Warning_MalformedWarnErrorList
  | Warning_MetaAlienNotATmUnknown
  | Warning_MultipleAscriptions
  | Warning_NondependentUserDefinedDataType
  | Warning_NonListLiteralSMTPattern
  | Warning_NormalizationFailure
  | Warning_NotDependentArrow
  | Warning_NotEmbedded
  | Warning_PatternMissingBoundVar
  | Warning_RecursiveDependency
  | Warning_RedundantExplicitCurrying
  | Warning_SMTPatTDeprecated
  | Warning_SMTPatternIllFormed
  | Warning_TopLevelEffect
  | Warning_UnboundModuleReference
  | Warning_UnexpectedFile
  | Warning_UnexpectedFsTypApp
  | Warning_UnexpectedZ3Output
  | Warning_UnprotectedTerm
  | Warning_UnrecognizedAttribute
  | Warning_UpperBoundCandidateAlreadyVisited
  | Warning_UseDefaultEffect
  | Warning_WrongErrorLocation
  | Warning_Z3InvocationWarning
  | Warning_PluginNotImplemented
  | Warning_MissingInterfaceOrImplementation
  | Warning_ConstructorBuildsUnexpectedType
  | Warning_ModuleOrFileNotFoundWarning
  | Error_NoLetMutable
  | Error_BadImplicit
  | Warning_DeprecatedDefinition
  | Fatal_SMTEncodingArityMismatch
  | Warning_Defensive
  | Warning_CantInspect
  | Warning_NilGivenExplicitArgs
  | Warning_ConsAppliedExplicitArgs
  | Warning_UnembedBinderKnot
  | Fatal_TacticProofRelevantGoal
  | Warning_TacAdmit
  | Fatal_IncoherentPatterns
  | Error_NoSMTButNeeded
  | Fatal_UnexpectedAntiquotation
  | Fatal_SplicedUndef
  | Fatal_SpliceUnembedFail
  | Warning_ExtractionUnexpectedEffect
  | Error_DidNotFail
  | Warning_UnappliedFail
  | Warning_QuantifierWithoutPattern
  | Error_EmptyFailErrs
  | Warning_logicqualifier
  | Fatal_CyclicDependence
  | Error_InductiveAnnotNotAType
  | Fatal_FriendInterface
  | Error_CannotRedefineConst
  | Error_BadClassDecl
  | Error_BadInductiveParam
  | Error_FieldShadow
  | Error_UnexpectedDM4FType
  | Fatal_EffectAbbreviationResultTypeMismatch
  | Error_AlreadyCachedAssertionFailure
  | Error_MustEraseMissing
  | Warning_EffectfulArgumentToErasedFunction
  | Fatal_EmptySurfaceLet
  | Warning_UnexpectedCheckedFile
  | Fatal_ExtractionUnsupported
  | Warning_SMTErrorReason
  | Warning_CoercionNotFound
  | Error_QuakeFailed
  | Error_IllSMTPat
  | Error_IllScopedTerm
  | Warning_UnusedLetRec
  | Fatal_Effects_Ordering_Coherence
  | Warning_BleedingEdge_Feature
  | Warning_IgnoredBinding
  | Warning_CouldNotReadHints
  | Fatal_BadUvar
  | Warning_WarnOnUse
  | Warning_DeprecatedAttributeSyntax
  | Warning_DeprecatedGeneric
  | Error_BadSplice
  | Error_UnexpectedUnresolvedUvar
  | Warning_UnfoldPlugin
  | Error_LayeredMissingAnnot
  | Error_CallToErased
  | Error_ErasedCtor
  | Error_RemoveUnusedTypeParameter
  | Warning_NoMagicInFSharp
  | Error_BadLetOpenRecord
  | Error_UnexpectedTypeclassInstance
  | Warning_AmbiguousResolveImplicitsHook
  | Warning_SplitAndRetryQueries
  | Warning_DeprecatedLightDoNotation
  | Warning_FailedToCheckInitialTacticGoal
  | Warning_Adhoc_IndexedEffect_Combinator
  | Error_PluginDynlink
  | Error_InternalQualifier
  | Warning_NameEscape
val uu___is_Error_DependencyAnalysisFailed : raw_error -> Prims.bool
val uu___is_Error_IDETooManyPops : raw_error -> Prims.bool
val uu___is_Error_IDEUnrecognized : raw_error -> Prims.bool
val uu___is_Error_InductiveTypeNotSatisfyPositivityCondition :
  raw_error -> Prims.bool
val uu___is_Error_InvalidUniverseVar : raw_error -> Prims.bool
val uu___is_Error_MissingFileName : raw_error -> Prims.bool
val uu___is_Error_ModuleFileNameMismatch : raw_error -> Prims.bool
val uu___is_Error_OpPlusInUniverse : raw_error -> Prims.bool
val uu___is_Error_OutOfRange : raw_error -> Prims.bool
val uu___is_Error_ProofObligationFailed : raw_error -> Prims.bool
val uu___is_Error_TooManyFiles : raw_error -> Prims.bool
val uu___is_Error_TypeCheckerFailToProve : raw_error -> Prims.bool
val uu___is_Error_TypeError : raw_error -> Prims.bool
val uu___is_Error_UncontrainedUnificationVar : raw_error -> Prims.bool
val uu___is_Error_UnexpectedGTotComputation : raw_error -> Prims.bool
val uu___is_Error_UnexpectedInstance : raw_error -> Prims.bool
val uu___is_Error_UnknownFatal_AssertionFailure : raw_error -> Prims.bool
val uu___is_Error_Z3InvocationError : raw_error -> Prims.bool
val uu___is_Error_IDEAssertionFailure : raw_error -> Prims.bool
val uu___is_Error_Z3SolverError : raw_error -> Prims.bool
val uu___is_Fatal_AbstractTypeDeclarationInInterface :
  raw_error -> Prims.bool
val uu___is_Fatal_ActionMustHaveFunctionType : raw_error -> Prims.bool
val uu___is_Fatal_AlreadyDefinedTopLevelDeclaration : raw_error -> Prims.bool
val uu___is_Fatal_ArgumentLengthMismatch : raw_error -> Prims.bool
val uu___is_Fatal_AssertionFailure : raw_error -> Prims.bool
val uu___is_Fatal_AssignToImmutableValues : raw_error -> Prims.bool
val uu___is_Fatal_AssumeValInInterface : raw_error -> Prims.bool
val uu___is_Fatal_BadlyInstantiatedSynthByTactic : raw_error -> Prims.bool
val uu___is_Fatal_BadSignatureShape : raw_error -> Prims.bool
val uu___is_Fatal_BinderAndArgsLengthMismatch : raw_error -> Prims.bool
val uu___is_Fatal_BothValAndLetInInterface : raw_error -> Prims.bool
val uu___is_Fatal_CardinalityConstraintViolated : raw_error -> Prims.bool
val uu___is_Fatal_ComputationNotTotal : raw_error -> Prims.bool
val uu___is_Fatal_ComputationTypeNotAllowed : raw_error -> Prims.bool
val uu___is_Fatal_ComputedTypeNotMatchAnnotation : raw_error -> Prims.bool
val uu___is_Fatal_ConstructorArgLengthMismatch : raw_error -> Prims.bool
val uu___is_Fatal_ConstructorFailedCheck : raw_error -> Prims.bool
val uu___is_Fatal_ConstructorNotFound : raw_error -> Prims.bool
val uu___is_Fatal_ConstsructorBuildWrongType : raw_error -> Prims.bool
val uu___is_Fatal_CycleInRecTypeAbbreviation : raw_error -> Prims.bool
val uu___is_Fatal_DataContructorNotFound : raw_error -> Prims.bool
val uu___is_Fatal_DefaultQualifierNotAllowedOnEffects :
  raw_error -> Prims.bool
val uu___is_Fatal_DefinitionNotFound : raw_error -> Prims.bool
val uu___is_Fatal_DisjuctivePatternVarsMismatch : raw_error -> Prims.bool
val uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal :
  raw_error -> Prims.bool
val uu___is_Fatal_DuplicateInImplementation : raw_error -> Prims.bool
val uu___is_Fatal_DuplicateModuleOrInterface : raw_error -> Prims.bool
val uu___is_Fatal_DuplicateTopLevelNames : raw_error -> Prims.bool
val uu___is_Fatal_DuplicateTypeAnnotationAndValDecl : raw_error -> Prims.bool
val uu___is_Fatal_EffectCannotBeReified : raw_error -> Prims.bool
val uu___is_Fatal_EffectConstructorNotFullyApplied : raw_error -> Prims.bool
val uu___is_Fatal_EffectfulAndPureComputationMismatch :
  raw_error -> Prims.bool
val uu___is_Fatal_EffectNotFound : raw_error -> Prims.bool
val uu___is_Fatal_EffectsCannotBeComposed : raw_error -> Prims.bool
val uu___is_Fatal_ErrorInSolveDeferredConstraints : raw_error -> Prims.bool
val uu___is_Fatal_ErrorsReported : raw_error -> Prims.bool
val uu___is_Fatal_EscapedBoundVar : raw_error -> Prims.bool
val uu___is_Fatal_ExpectedArrowAnnotatedType : raw_error -> Prims.bool
val uu___is_Fatal_ExpectedGhostExpression : raw_error -> Prims.bool
val uu___is_Fatal_ExpectedPureExpression : raw_error -> Prims.bool
val uu___is_Fatal_ExpectNormalizedEffect : raw_error -> Prims.bool
val uu___is_Fatal_ExpectTermGotFunction : raw_error -> Prims.bool
val uu___is_Fatal_ExpectTrivialPreCondition : raw_error -> Prims.bool
val uu___is_Fatal_FailToCompileNativeTactic : raw_error -> Prims.bool
val uu___is_Fatal_FailToExtractNativeTactic : raw_error -> Prims.bool
val uu___is_Fatal_FailToProcessPragma : raw_error -> Prims.bool
val uu___is_Fatal_FailToResolveImplicitArgument : raw_error -> Prims.bool
val uu___is_Fatal_FailToSolveUniverseInEquality : raw_error -> Prims.bool
val uu___is_Fatal_FieldsNotBelongToSameRecordType : raw_error -> Prims.bool
val uu___is_Fatal_ForbiddenReferenceToCurrentModule : raw_error -> Prims.bool
val uu___is_Fatal_FreeVariables : raw_error -> Prims.bool
val uu___is_Fatal_FunctionTypeExpected : raw_error -> Prims.bool
val uu___is_Fatal_IdentifierNotFound : raw_error -> Prims.bool
val uu___is_Fatal_IllAppliedConstant : raw_error -> Prims.bool
val uu___is_Fatal_IllegalCharInByteArray : raw_error -> Prims.bool
val uu___is_Fatal_IllegalCharInOperatorName : raw_error -> Prims.bool
val uu___is_Fatal_IllTyped : raw_error -> Prims.bool
val uu___is_Fatal_ImpossibleAbbrevLidBundle : raw_error -> Prims.bool
val uu___is_Fatal_ImpossibleAbbrevRenameBundle : raw_error -> Prims.bool
val uu___is_Fatal_ImpossibleInductiveWithAbbrev : raw_error -> Prims.bool
val uu___is_Fatal_ImpossiblePrePostAbs : raw_error -> Prims.bool
val uu___is_Fatal_ImpossiblePrePostArrow : raw_error -> Prims.bool
val uu___is_Fatal_ImpossibleToGenerateDMEffect : raw_error -> Prims.bool
val uu___is_Fatal_ImpossibleTypeAbbrevBundle : raw_error -> Prims.bool
val uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle : raw_error -> Prims.bool
val uu___is_Fatal_IncludeModuleNotPrepared : raw_error -> Prims.bool
val uu___is_Fatal_IncoherentInlineUniverse : raw_error -> Prims.bool
val uu___is_Fatal_IncompatibleKinds : raw_error -> Prims.bool
val uu___is_Fatal_IncompatibleNumberOfTypes : raw_error -> Prims.bool
val uu___is_Fatal_IncompatibleSetOfUniverse : raw_error -> Prims.bool
val uu___is_Fatal_IncompatibleUniverse : raw_error -> Prims.bool
val uu___is_Fatal_InconsistentImplicitArgumentAnnotation :
  raw_error -> Prims.bool
val uu___is_Fatal_InconsistentImplicitQualifier : raw_error -> Prims.bool
val uu___is_Fatal_InconsistentQualifierAnnotation : raw_error -> Prims.bool
val uu___is_Fatal_InferredTypeCauseVarEscape : raw_error -> Prims.bool
val uu___is_Fatal_InlineRenamedAsUnfold : raw_error -> Prims.bool
val uu___is_Fatal_InsufficientPatternArguments : raw_error -> Prims.bool
val uu___is_Fatal_InterfaceAlreadyProcessed : raw_error -> Prims.bool
val uu___is_Fatal_InterfaceNotImplementedByModule : raw_error -> Prims.bool
val uu___is_Fatal_InterfaceWithTypeImplementation : raw_error -> Prims.bool
val uu___is_Fatal_InvalidFloatingPointNumber : raw_error -> Prims.bool
val uu___is_Fatal_InvalidFSDocKeyword : raw_error -> Prims.bool
val uu___is_Fatal_InvalidIdentifier : raw_error -> Prims.bool
val uu___is_Fatal_InvalidLemmaArgument : raw_error -> Prims.bool
val uu___is_Fatal_InvalidNumericLiteral : raw_error -> Prims.bool
val uu___is_Fatal_InvalidRedefinitionOfLexT : raw_error -> Prims.bool
val uu___is_Fatal_InvalidUnicodeInStringLiteral : raw_error -> Prims.bool
val uu___is_Fatal_InvalidUTF8Encoding : raw_error -> Prims.bool
val uu___is_Fatal_InvalidWarnErrorSetting : raw_error -> Prims.bool
val uu___is_Fatal_LetBoundMonadicMismatch : raw_error -> Prims.bool
val uu___is_Fatal_LetMutableForVariablesOnly : raw_error -> Prims.bool
val uu___is_Fatal_LetOpenModuleOnly : raw_error -> Prims.bool
val uu___is_Fatal_LetRecArgumentMismatch : raw_error -> Prims.bool
val uu___is_Fatal_MalformedActionDeclaration : raw_error -> Prims.bool
val uu___is_Fatal_MismatchedPatternType : raw_error -> Prims.bool
val uu___is_Fatal_MismatchUniversePolymorphic : raw_error -> Prims.bool
val uu___is_Fatal_MissingDataConstructor : raw_error -> Prims.bool
val uu___is_Fatal_MissingExposeInterfacesOption : raw_error -> Prims.bool
val uu___is_Fatal_MissingFieldInRecord : raw_error -> Prims.bool
val uu___is_Fatal_MissingImplementation : raw_error -> Prims.bool
val uu___is_Fatal_MissingImplicitArguments : raw_error -> Prims.bool
val uu___is_Fatal_MissingInterface : raw_error -> Prims.bool
val uu___is_Fatal_MissingNameInBinder : raw_error -> Prims.bool
val uu___is_Fatal_MissingPrimsModule : raw_error -> Prims.bool
val uu___is_Fatal_MissingQuantifierBinder : raw_error -> Prims.bool
val uu___is_Fatal_ModuleExpected : raw_error -> Prims.bool
val uu___is_Fatal_ModuleFileNotFound : raw_error -> Prims.bool
val uu___is_Fatal_ModuleFirstStatement : raw_error -> Prims.bool
val uu___is_Fatal_ModuleNotFound : raw_error -> Prims.bool
val uu___is_Fatal_ModuleOrFileNotFound : raw_error -> Prims.bool
val uu___is_Fatal_MonadAlreadyDefined : raw_error -> Prims.bool
val uu___is_Fatal_MoreThanOneDeclaration : raw_error -> Prims.bool
val uu___is_Fatal_MultipleLetBinding : raw_error -> Prims.bool
val uu___is_Fatal_NameNotFound : raw_error -> Prims.bool
val uu___is_Fatal_NameSpaceNotFound : raw_error -> Prims.bool
val uu___is_Fatal_NegativeUniverseConstFatal_NotSupported :
  raw_error -> Prims.bool
val uu___is_Fatal_NoFileProvided : raw_error -> Prims.bool
val uu___is_Fatal_NonInductiveInMutuallyDefinedType : raw_error -> Prims.bool
val uu___is_Fatal_NonLinearPatternNotPermitted : raw_error -> Prims.bool
val uu___is_Fatal_NonLinearPatternVars : raw_error -> Prims.bool
val uu___is_Fatal_NonSingletonTopLevel : raw_error -> Prims.bool
val uu___is_Fatal_NonSingletonTopLevelModule : raw_error -> Prims.bool
val uu___is_Error_NonTopRecFunctionNotFullyEncoded : raw_error -> Prims.bool
val uu___is_Fatal_NonTrivialPreConditionInPrims : raw_error -> Prims.bool
val uu___is_Fatal_NonVariableInductiveTypeParameter : raw_error -> Prims.bool
val uu___is_Fatal_NotApplicationOrFv : raw_error -> Prims.bool
val uu___is_Fatal_NotEnoughArgsToEffect : raw_error -> Prims.bool
val uu___is_Fatal_NotEnoughArgumentsForEffect : raw_error -> Prims.bool
val uu___is_Fatal_NotFunctionType : raw_error -> Prims.bool
val uu___is_Fatal_NotSupported : raw_error -> Prims.bool
val uu___is_Fatal_NotTopLevelModule : raw_error -> Prims.bool
val uu___is_Fatal_NotValidFStarFile : raw_error -> Prims.bool
val uu___is_Fatal_NotValidIncludeDirectory : raw_error -> Prims.bool
val uu___is_Fatal_OneModulePerFile : raw_error -> Prims.bool
val uu___is_Fatal_OpenGoalsInSynthesis : raw_error -> Prims.bool
val uu___is_Fatal_OptionsNotCompatible : raw_error -> Prims.bool
val uu___is_Fatal_OutOfOrder : raw_error -> Prims.bool
val uu___is_Fatal_ParseErrors : raw_error -> Prims.bool
val uu___is_Fatal_ParseItError : raw_error -> Prims.bool
val uu___is_Fatal_PolyTypeExpected : raw_error -> Prims.bool
val uu___is_Fatal_PossibleInfiniteTyp : raw_error -> Prims.bool
val uu___is_Fatal_PreModuleMismatch : raw_error -> Prims.bool
val uu___is_Fatal_QulifierListNotPermitted : raw_error -> Prims.bool
val uu___is_Fatal_RecursiveFunctionLiteral : raw_error -> Prims.bool
val uu___is_Fatal_ReflectOnlySupportedOnEffects : raw_error -> Prims.bool
val uu___is_Fatal_ReservedPrefix : raw_error -> Prims.bool
val uu___is_Fatal_SMTOutputParseError : raw_error -> Prims.bool
val uu___is_Fatal_SMTSolverError : raw_error -> Prims.bool
val uu___is_Fatal_SyntaxError : raw_error -> Prims.bool
val uu___is_Fatal_SynthByTacticError : raw_error -> Prims.bool
val uu___is_Fatal_TacticGotStuck : raw_error -> Prims.bool
val uu___is_Fatal_TcOneFragmentFailed : raw_error -> Prims.bool
val uu___is_Fatal_TermOutsideOfDefLanguage : raw_error -> Prims.bool
val uu___is_Fatal_ToManyArgumentToFunction : raw_error -> Prims.bool
val uu___is_Fatal_TooManyOrTooFewFileMatch : raw_error -> Prims.bool
val uu___is_Fatal_TooManyPatternArguments : raw_error -> Prims.bool
val uu___is_Fatal_TooManyUniverse : raw_error -> Prims.bool
val uu___is_Fatal_TypeMismatch : raw_error -> Prims.bool
val uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly :
  raw_error -> Prims.bool
val uu___is_Fatal_UnableToReadFile : raw_error -> Prims.bool
val uu___is_Fatal_UnepxectedOrUnboundOperator : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedBinder : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedBindShape : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedChar : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedComputationTypeForLetRec :
  raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedConstructorType : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedDataConstructor : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedEffect : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedEmptyRecord : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedExpressionType : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedFunctionParameterType : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedGeneralizedUniverse : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedGTotForLetRec : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedGuard : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedIdentifier : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedImplicitArgument : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedImplictArgument : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedInductivetype : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedLetBinding : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedModuleDeclaration : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedNumberOfUniverse : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedNumericLiteral : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedPattern : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedPosition : raw_error -> Prims.bool
val uu___is_Fatal_UnExpectedPreCondition : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedReturnShape : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedSignatureForMonad : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedTerm : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedTermInUniverse : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedTermType : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedTermVQuote : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedUniversePolymorphicReturn :
  raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedUniverseVariable : raw_error -> Prims.bool
val uu___is_Fatal_UnfoldableDeprecated : raw_error -> Prims.bool
val uu___is_Fatal_UnificationNotWellFormed : raw_error -> Prims.bool
val uu___is_Fatal_Uninstantiated : raw_error -> Prims.bool
val uu___is_Error_UninstantiatedUnificationVarInTactic :
  raw_error -> Prims.bool
val uu___is_Fatal_UninstantiatedVarInTactic : raw_error -> Prims.bool
val uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars :
  raw_error -> Prims.bool
val uu___is_Fatal_UniversePolymorphicInnerLetBound : raw_error -> Prims.bool
val uu___is_Fatal_UnknownAttribute : raw_error -> Prims.bool
val uu___is_Fatal_UnknownToolForDep : raw_error -> Prims.bool
val uu___is_Fatal_UnrecognizedExtension : raw_error -> Prims.bool
val uu___is_Fatal_UnresolvedPatternVar : raw_error -> Prims.bool
val uu___is_Fatal_UnsupportedConstant : raw_error -> Prims.bool
val uu___is_Fatal_UnsupportedDisjuctivePatterns : raw_error -> Prims.bool
val uu___is_Fatal_UnsupportedQualifier : raw_error -> Prims.bool
val uu___is_Fatal_UserTacticFailure : raw_error -> Prims.bool
val uu___is_Fatal_ValueRestriction : raw_error -> Prims.bool
val uu___is_Fatal_VariableNotFound : raw_error -> Prims.bool
val uu___is_Fatal_WrongBodyTypeForReturnWP : raw_error -> Prims.bool
val uu___is_Fatal_WrongDataAppHeadFormat : raw_error -> Prims.bool
val uu___is_Fatal_WrongDefinitionOrder : raw_error -> Prims.bool
val uu___is_Fatal_WrongResultTypeAfterConstrutor : raw_error -> Prims.bool
val uu___is_Fatal_WrongTerm : raw_error -> Prims.bool
val uu___is_Fatal_WhenClauseNotSupported : raw_error -> Prims.bool
val uu___is_Unused01 : raw_error -> Prims.bool
val uu___is_Warning_AddImplicitAssumeNewQualifier : raw_error -> Prims.bool
val uu___is_Warning_AdmitWithoutDefinition : raw_error -> Prims.bool
val uu___is_Warning_CachedFile : raw_error -> Prims.bool
val uu___is_Warning_DefinitionNotTranslated : raw_error -> Prims.bool
val uu___is_Warning_DependencyFound : raw_error -> Prims.bool
val uu___is_Warning_DeprecatedEqualityOnBinder : raw_error -> Prims.bool
val uu___is_Warning_DeprecatedOpaqueQualifier : raw_error -> Prims.bool
val uu___is_Warning_DocOverwrite : raw_error -> Prims.bool
val uu___is_Warning_FileNotWritten : raw_error -> Prims.bool
val uu___is_Warning_Filtered : raw_error -> Prims.bool
val uu___is_Warning_FunctionLiteralPrecisionLoss : raw_error -> Prims.bool
val uu___is_Warning_FunctionNotExtacted : raw_error -> Prims.bool
val uu___is_Warning_HintFailedToReplayProof : raw_error -> Prims.bool
val uu___is_Warning_HitReplayFailed : raw_error -> Prims.bool
val uu___is_Warning_IDEIgnoreCodeGen : raw_error -> Prims.bool
val uu___is_Warning_IllFormedGoal : raw_error -> Prims.bool
val uu___is_Warning_InaccessibleArgument : raw_error -> Prims.bool
val uu___is_Warning_IncoherentImplicitQualifier : raw_error -> Prims.bool
val uu___is_Warning_IrrelevantQualifierOnArgumentToReflect :
  raw_error -> Prims.bool
val uu___is_Warning_IrrelevantQualifierOnArgumentToReify :
  raw_error -> Prims.bool
val uu___is_Warning_MalformedWarnErrorList : raw_error -> Prims.bool
val uu___is_Warning_MetaAlienNotATmUnknown : raw_error -> Prims.bool
val uu___is_Warning_MultipleAscriptions : raw_error -> Prims.bool
val uu___is_Warning_NondependentUserDefinedDataType : raw_error -> Prims.bool
val uu___is_Warning_NonListLiteralSMTPattern : raw_error -> Prims.bool
val uu___is_Warning_NormalizationFailure : raw_error -> Prims.bool
val uu___is_Warning_NotDependentArrow : raw_error -> Prims.bool
val uu___is_Warning_NotEmbedded : raw_error -> Prims.bool
val uu___is_Warning_PatternMissingBoundVar : raw_error -> Prims.bool
val uu___is_Warning_RecursiveDependency : raw_error -> Prims.bool
val uu___is_Warning_RedundantExplicitCurrying : raw_error -> Prims.bool
val uu___is_Warning_SMTPatTDeprecated : raw_error -> Prims.bool
val uu___is_Warning_SMTPatternIllFormed : raw_error -> Prims.bool
val uu___is_Warning_TopLevelEffect : raw_error -> Prims.bool
val uu___is_Warning_UnboundModuleReference : raw_error -> Prims.bool
val uu___is_Warning_UnexpectedFile : raw_error -> Prims.bool
val uu___is_Warning_UnexpectedFsTypApp : raw_error -> Prims.bool
val uu___is_Warning_UnexpectedZ3Output : raw_error -> Prims.bool
val uu___is_Warning_UnprotectedTerm : raw_error -> Prims.bool
val uu___is_Warning_UnrecognizedAttribute : raw_error -> Prims.bool
val uu___is_Warning_UpperBoundCandidateAlreadyVisited :
  raw_error -> Prims.bool
val uu___is_Warning_UseDefaultEffect : raw_error -> Prims.bool
val uu___is_Warning_WrongErrorLocation : raw_error -> Prims.bool
val uu___is_Warning_Z3InvocationWarning : raw_error -> Prims.bool
val uu___is_Warning_PluginNotImplemented : raw_error -> Prims.bool
val uu___is_Warning_MissingInterfaceOrImplementation :
  raw_error -> Prims.bool
val uu___is_Warning_ConstructorBuildsUnexpectedType : raw_error -> Prims.bool
val uu___is_Warning_ModuleOrFileNotFoundWarning : raw_error -> Prims.bool
val uu___is_Error_NoLetMutable : raw_error -> Prims.bool
val uu___is_Error_BadImplicit : raw_error -> Prims.bool
val uu___is_Warning_DeprecatedDefinition : raw_error -> Prims.bool
val uu___is_Fatal_SMTEncodingArityMismatch : raw_error -> Prims.bool
val uu___is_Warning_Defensive : raw_error -> Prims.bool
val uu___is_Warning_CantInspect : raw_error -> Prims.bool
val uu___is_Warning_NilGivenExplicitArgs : raw_error -> Prims.bool
val uu___is_Warning_ConsAppliedExplicitArgs : raw_error -> Prims.bool
val uu___is_Warning_UnembedBinderKnot : raw_error -> Prims.bool
val uu___is_Fatal_TacticProofRelevantGoal : raw_error -> Prims.bool
val uu___is_Warning_TacAdmit : raw_error -> Prims.bool
val uu___is_Fatal_IncoherentPatterns : raw_error -> Prims.bool
val uu___is_Error_NoSMTButNeeded : raw_error -> Prims.bool
val uu___is_Fatal_UnexpectedAntiquotation : raw_error -> Prims.bool
val uu___is_Fatal_SplicedUndef : raw_error -> Prims.bool
val uu___is_Fatal_SpliceUnembedFail : raw_error -> Prims.bool
val uu___is_Warning_ExtractionUnexpectedEffect : raw_error -> Prims.bool
val uu___is_Error_DidNotFail : raw_error -> Prims.bool
val uu___is_Warning_UnappliedFail : raw_error -> Prims.bool
val uu___is_Warning_QuantifierWithoutPattern : raw_error -> Prims.bool
val uu___is_Error_EmptyFailErrs : raw_error -> Prims.bool
val uu___is_Warning_logicqualifier : raw_error -> Prims.bool
val uu___is_Fatal_CyclicDependence : raw_error -> Prims.bool
val uu___is_Error_InductiveAnnotNotAType : raw_error -> Prims.bool
val uu___is_Fatal_FriendInterface : raw_error -> Prims.bool
val uu___is_Error_CannotRedefineConst : raw_error -> Prims.bool
val uu___is_Error_BadClassDecl : raw_error -> Prims.bool
val uu___is_Error_BadInductiveParam : raw_error -> Prims.bool
val uu___is_Error_FieldShadow : raw_error -> Prims.bool
val uu___is_Error_UnexpectedDM4FType : raw_error -> Prims.bool
val uu___is_Fatal_EffectAbbreviationResultTypeMismatch :
  raw_error -> Prims.bool
val uu___is_Error_AlreadyCachedAssertionFailure : raw_error -> Prims.bool
val uu___is_Error_MustEraseMissing : raw_error -> Prims.bool
val uu___is_Warning_EffectfulArgumentToErasedFunction :
  raw_error -> Prims.bool
val uu___is_Fatal_EmptySurfaceLet : raw_error -> Prims.bool
val uu___is_Warning_UnexpectedCheckedFile : raw_error -> Prims.bool
val uu___is_Fatal_ExtractionUnsupported : raw_error -> Prims.bool
val uu___is_Warning_SMTErrorReason : raw_error -> Prims.bool
val uu___is_Warning_CoercionNotFound : raw_error -> Prims.bool
val uu___is_Error_QuakeFailed : raw_error -> Prims.bool
val uu___is_Error_IllSMTPat : raw_error -> Prims.bool
val uu___is_Error_IllScopedTerm : raw_error -> Prims.bool
val uu___is_Warning_UnusedLetRec : raw_error -> Prims.bool
val uu___is_Fatal_Effects_Ordering_Coherence : raw_error -> Prims.bool
val uu___is_Warning_BleedingEdge_Feature : raw_error -> Prims.bool
val uu___is_Warning_IgnoredBinding : raw_error -> Prims.bool
val uu___is_Warning_CouldNotReadHints : raw_error -> Prims.bool
val uu___is_Fatal_BadUvar : raw_error -> Prims.bool
val uu___is_Warning_WarnOnUse : raw_error -> Prims.bool
val uu___is_Warning_DeprecatedAttributeSyntax : raw_error -> Prims.bool
val uu___is_Warning_DeprecatedGeneric : raw_error -> Prims.bool
val uu___is_Error_BadSplice : raw_error -> Prims.bool
val uu___is_Error_UnexpectedUnresolvedUvar : raw_error -> Prims.bool
val uu___is_Warning_UnfoldPlugin : raw_error -> Prims.bool
val uu___is_Error_LayeredMissingAnnot : raw_error -> Prims.bool
val uu___is_Error_CallToErased : raw_error -> Prims.bool
val uu___is_Error_ErasedCtor : raw_error -> Prims.bool
val uu___is_Error_RemoveUnusedTypeParameter : raw_error -> Prims.bool
val uu___is_Warning_NoMagicInFSharp : raw_error -> Prims.bool
val uu___is_Error_BadLetOpenRecord : raw_error -> Prims.bool
val uu___is_Error_UnexpectedTypeclassInstance : raw_error -> Prims.bool
val uu___is_Warning_AmbiguousResolveImplicitsHook : raw_error -> Prims.bool
val uu___is_Warning_SplitAndRetryQueries : raw_error -> Prims.bool
val uu___is_Warning_DeprecatedLightDoNotation : raw_error -> Prims.bool
val uu___is_Warning_FailedToCheckInitialTacticGoal : raw_error -> Prims.bool
val uu___is_Warning_Adhoc_IndexedEffect_Combinator : raw_error -> Prims.bool
val uu___is_Error_PluginDynlink : raw_error -> Prims.bool
val uu___is_Error_InternalQualifier : raw_error -> Prims.bool
val uu___is_Warning_NameEscape : raw_error -> Prims.bool
type error_setting = raw_error * error_flag * Prims.int
val default_settings : error_setting Prims.list
