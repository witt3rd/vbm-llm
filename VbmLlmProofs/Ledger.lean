import VbmLlmProofs.Wire
import VbmLlmProofs.Finish
import VbmLlmProofs.Usage
import VbmLlmProofs.OpenAI.Response
import VbmLlmProofs.OpenAI.Stream
import VbmLlmProofs.OpenAI.Request
import VbmLlmProofs.Turn
import VbmLlmProofs.Error
import VbmLlmProofs.OpenRouter
import VbmLlmProofs.Anthropic.Response
import VbmLlmProofs.Anthropic.Request
import VbmLlmProofs.Anthropic.RequestDecode
/-! # The obligation ledger

Every claim the library makes, keyed by a slug. A claim is `proved` only by naming theorems (double-backtick names are checked at elaboration, so a renamed or deleted theorem breaks this file),
`partly` when theorems cover only a part (the note says which part is open), `open_` when nothing is proved, or `limit` when no machine decides it (the note says who carries it).
Each claim may carry **spec-clause tags** `convention:clause-id` naming the clauses of the pinned convention (`docs/clause-index.txt`) it is about.
`scripts/LedgerGate.lean` renders `docs/proof-ledger.md` from this list, checks the tags against the index and ratchets the counts: proved may only rise, open may only fall, clause coverage may only rise.
A report may not call anything verified that is not `proved`. -/

inductive Status where
  | proved (thms : List Lean.Name)
  | partly (thms : List Lean.Name) (open_ : String)
  | open_ (note : String)
  | limit (carriedBy : String)

structure Obligation where
  slug    : String
  clauses : List String
  status  : Status

def O (slug : String) (clauses : List String) (s : Status) : Obligation := ⟨slug, clauses, s⟩

def ledger : List Obligation := [
  -- reading a parsed value
  O "wire-duplicate-key-later-wins" [] (.proved [``VbmLlm.lookup_snoc, ``VbmLlm.lookup_absent, ``VbmLlm.lookup_eq, ``VbmLlm.get_nonobj]),
  O "wire-a-count-is-a-plain-natural" [] (.proved [``VbmLlm.natOf_neg, ``VbmLlm.natOf_frac, ``VbmLlm.natOf_exp, ``VbmLlm.natOf_zero, ``VbmLlm.natOf_nz, ``VbmLlm.natOf_120, ``VbmLlm.nat?_nonnum]),
  -- the OpenAI chat-completions response
  O "openai-reply-decode-is-characterised" ["openai-chat:CreateChatCompletionResponse.id", "openai-chat:CreateChatCompletionResponse.model", "openai-chat:CreateChatCompletionResponse.choices.index"]
    (.proved [``VbmLlm.OpenAI.decode_ok_iff, ``VbmLlm.OpenAI.decodeChoice_ok_iff, ``VbmLlm.OpenAI.decodeChoices_ok_iff]),
  O "openai-reply-must-be-an-object" ["openai-chat:CreateChatCompletionResponse.choices"] (.proved [``VbmLlm.OpenAI.decode_not_object]),
  O "openai-choices-required-array-and-non-empty" ["openai-chat:CreateChatCompletionResponse.choices"]
    (.proved [``VbmLlm.OpenAI.decode_no_choices, ``VbmLlm.OpenAI.decode_empty_choices, ``VbmLlm.OpenAI.decode_choices_not_array, ``VbmLlm.OpenAI.decodeChoicesField_ok_iff]),
  O "openai-choice-requires-a-message" ["openai-chat:CreateChatCompletionResponse.choices.message"] (.proved [``VbmLlm.OpenAI.decodeChoice_no_message_refused, ``VbmLlm.OpenAI.decodeChoice_ok_iff]),
  O "openai-message-text-is-string-or-null" ["openai-chat:ChatCompletionResponseMessage.content", "openai-chat:ChatCompletionResponseMessage.refusal"]
    (.proved [``VbmLlm.OpenAI.decodeMessage_ok_iff, ``VbmLlm.OpenAI.optStr_ok_iff, ``VbmLlm.OpenAI.optStr_wrong]),
  O "openai-tool-calls-absent-or-an-array-of-calls" ["openai-chat:ChatCompletionResponseMessage.tool_calls"] (.proved [``VbmLlm.OpenAI.decodeCalls_ok_iff, ``VbmLlm.OpenAI.decodeToolCalls_ok_iff]),
  O "openai-tool-call-shape" ["openai-chat:ChatCompletionMessageToolCall.id", "openai-chat:ChatCompletionMessageToolCall.function.name", "openai-chat:ChatCompletionMessageToolCall.function.arguments"]
    (.proved [``VbmLlm.OpenAI.decodeToolCall_ok_iff, ``VbmLlm.OpenAI.decodeToolCall_no_function_refused]),
  O "openai-tool-call-other-types-refused" ["openai-chat:ChatCompletionMessageToolCall.type"]
    (.proved [``VbmLlm.OpenAI.checkType_ok_iff, ``VbmLlm.OpenAI.checkType_unsupported, ``VbmLlm.OpenAI.decodeToolCall_custom_refused]),
  O "openai-tool-arguments-are-verbatim-text" ["openai-chat:ChatCompletionMessageToolCall.function.arguments"] (.proved [``VbmLlm.OpenAI.decodeToolCall_ok_iff]),
  O "openai-usage-counts-are-plain-naturals" ["openai-chat:CreateChatCompletionResponse.usage", "openai-chat:CompletionUsage.prompt_tokens", "openai-chat:CompletionUsage.completion_tokens",
      "openai-chat:CompletionUsage.total_tokens", "openai-chat:CompletionUsage.prompt_tokens_details.cached_tokens", "openai-chat:CompletionUsage.completion_tokens_details.reasoning_tokens"]
    (.proved [``VbmLlm.OpenAI.decodeUsage_ok_iff, ``VbmLlm.OpenAI.decodeUsageOpt_ok_iff, ``VbmLlm.OpenAI.optNat_ok_iff, ``VbmLlm.OpenAI.optNat_wrong, ``VbmLlm.OpenAI.optDetail_ok_iff]),
  O "openai-no-coercion" ["openai-chat:CreateChatCompletionResponse.id"]
    (.proved [``VbmLlm.OpenAI.decode_id_wrong_type, ``VbmLlm.OpenAI.optStr_wrong, ``VbmLlm.OpenAI.optNat_wrong, ``VbmLlm.OpenAI.reqStr_wrong, ``VbmLlm.OpenAI.reqObj_wrong]),
  O "openai-finish-reason-is-kept-as-text-and-classed-totally" ["openai-chat:CreateChatCompletionResponse.choices.finish_reason"]
    (.proved [``VbmLlm.FinishClass.ofOpenAI_stop, ``VbmLlm.FinishClass.ofOpenAI_length, ``VbmLlm.FinishClass.ofOpenAI_tool_calls, ``VbmLlm.FinishClass.ofOpenAI_function_call,
      ``VbmLlm.FinishClass.ofOpenAI_content_filter, ``VbmLlm.FinishClass.ofOpenAI_unknown, ``VbmLlm.FinishClass.ofOpenAI_truncated_iff]),
  -- usage arithmetic
  O "usage-openai-prompt-includes-the-cache" ["openai-chat:CompletionUsage.prompt_tokens", "openai-chat:CompletionUsage.prompt_tokens_details.cached_tokens"]
    (.proved [``VbmLlm.OpenAI.tokens_ok_iff, ``VbmLlm.OpenAI.openai_input_eq_prompt, ``VbmLlm.OpenAI.openai_uncached, ``VbmLlm.OpenAI.openai_read, ``VbmLlm.OpenAI.openai_no_write, ``VbmLlm.OpenAI.openai_output, ``VbmLlm.OpenAI.openai_total]),
  O "usage-a-contradictory-report-is-refused-not-clamped" ["openai-chat:CompletionUsage.completion_tokens_details.reasoning_tokens"]
    (.proved [``VbmLlm.OpenAI.openai_cached_exceeds_refused, ``VbmLlm.OpenAI.openai_reasoning_exceeds_refused]),
  O "usage-totals-add-over-a-turn-and-a-run" [] (.proved [``VbmLlm.Tokens.add_comm, ``VbmLlm.Tokens.add_assoc, ``VbmLlm.Tokens.zero_add, ``VbmLlm.Tokens.add_zero, ``VbmLlm.Tokens.input_add, ``VbmLlm.Tokens.total_add]),
  O "usage-a-frame-with-no-report-adds-nothing" [] (.proved [``VbmLlm.OpenAI.openai_empty, ``VbmLlm.Tokens.zero_add]),
  -- the error taxonomy and the body of a failed call
  O "error-the-status-of-a-failed-call-has-a-class" ["openai-chat-status:auth", "openai-chat-status:quota", "openai-chat-status:timeout", "openai-chat-status:rate-limit", "openai-chat-status:server"]
    (.proved [``VbmLlm.ErrorClass.ofStatus_auth, ``VbmLlm.ErrorClass.ofStatus_quota, ``VbmLlm.ErrorClass.ofStatus_timeout, ``VbmLlm.ErrorClass.ofStatus_rateLimit, ``VbmLlm.ErrorClass.ofStatus_tls, ``VbmLlm.ErrorClass.ofStatus_server]),
  O "error-an-overflow-is-a-client-error-the-consumer-reads-so" ["openai-chat-status:overflow"] (.proved [``VbmLlm.ErrorClass.ofStatus_overflow_iff, ``VbmLlm.ErrorClass.ofStatus_no_words]),
  O "openai-error-body-is-read-as-the-schema-says-and-never-coerced" ["openai-chat:ErrorResponse.error", "openai-chat:Error.message", "openai-chat:Error.type", "openai-chat:Error.param", "openai-chat:Error.code"]
    (.proved [``VbmLlm.decodeApiError_ok_iff, ``VbmLlm.decodeApiError_not_object, ``VbmLlm.decodeApiError_no_error, ``VbmLlm.decodeApiError_no_message, ``VbmLlm.decodeApiError_code_wrong]),
  -- not yet built (open) and not decidable by a machine (limit)
  -- the OpenAI chat-completions request: encoder, decoder, round trip
  O "openai-request-members-are-the-fields" ["openai-chat:CreateChatCompletionRequest.model", "openai-chat:CreateChatCompletionRequest.messages", "openai-chat:CreateChatCompletionRequest.tools", "openai-chat:CreateChatCompletionRequest.tool_choice", "openai-chat:CreateChatCompletionRequest.parallel_tool_calls", "openai-chat:CreateChatCompletionRequest.stream", "openai-chat:ChatCompletionStreamOptions.include_usage",
      "openai-chat:CreateChatCompletionRequest.max_completion_tokens", "openai-chat:CreateChatCompletionRequest.max_tokens", "openai-chat:CreateChatCompletionRequest.temperature", "openai-chat:CreateChatCompletionRequest.top_p"]
    (.proved [``VbmLlm.OpenAI.encode_get_model, ``VbmLlm.OpenAI.encode_get_messages, ``VbmLlm.OpenAI.encode_get_tools, ``VbmLlm.OpenAI.encode_get_tool_choice, ``VbmLlm.OpenAI.encode_get_parallel_tool_calls,
      ``VbmLlm.OpenAI.encode_get_stream, ``VbmLlm.OpenAI.encode_get_stream_options, ``VbmLlm.OpenAI.encode_get_max_completion_tokens, ``VbmLlm.OpenAI.encode_get_max_tokens, ``VbmLlm.OpenAI.encode_get_temperature,
      ``VbmLlm.OpenAI.encode_get_top_p, ``VbmLlm.OpenAI.encode_object]),
  O "openai-request-an-absent-field-is-left-out-never-null" ["openai-chat:CreateChatCompletionRequest.tools", "openai-chat:CreateChatCompletionRequest.tool_choice", "openai-chat:CreateChatCompletionRequest.max_completion_tokens"] (.proved [``VbmLlm.OpenAI.encode_members_not_null, ``VbmLlm.OpenAI.mem_opt]),
  O "openai-request-counts-are-plain-naturals" ["openai-chat:CreateChatCompletionRequest.max_completion_tokens", "openai-chat:CreateChatCompletionRequest.max_tokens"] (.proved [``VbmLlm.OpenAI.natOf_natNumber, ``VbmLlm.OpenAI.leadRest_val]),
  O "openai-request-tool-calls-are-written-as-read" ["openai-chat:ChatCompletionRequestAssistantMessage.tool_calls"] (.proved [``VbmLlm.OpenAI.decodeToolCall_encodeToolCall]),
  O "openai-request-codec-round-trip" ["openai-chat:CreateChatCompletionRequest.model", "openai-chat:CreateChatCompletionRequest.messages", "openai-chat:ChatCompletionRequestSystemMessage.content", "openai-chat:ChatCompletionRequestDeveloperMessage.content", "openai-chat:ChatCompletionRequestUserMessage.content",
      "openai-chat:ChatCompletionRequestAssistantMessage.content", "openai-chat:ChatCompletionRequestAssistantMessage.tool_calls", "openai-chat:ChatCompletionRequestToolMessage.tool_call_id", "openai-chat:ChatCompletionRequestToolMessage.content",
      "openai-chat:ChatCompletionTool.type", "openai-chat:FunctionObject.name", "openai-chat:FunctionObject.description", "openai-chat:FunctionObject.parameters", "openai-chat:FunctionObject.strict",
      "openai-chat:ChatCompletionNamedToolChoice.function.name", "openai-chat:CreateChatCompletionRequest.tool_choice", "openai-chat:CreateChatCompletionRequest.tools"]
    (.proved [``VbmLlm.OpenAI.decode_encode, ``VbmLlm.OpenAI.decodeReqMessage_encodeMessage, ``VbmLlm.OpenAI.decodeTool_encodeTool, ``VbmLlm.OpenAI.decodeMessages_encode, ``VbmLlm.OpenAI.decodeTools_encode,
      ``VbmLlm.OpenAI.decodeToolChoice_encode, ``VbmLlm.OpenAI.decodeIncludeUsage_encode, ``VbmLlm.OpenAI.decodeEach_encode, ``VbmLlm.OpenAI.decodeToolCalls_encode, ``VbmLlm.OpenAI.optBool_orNull,
      ``VbmLlm.OpenAI.optNat_orNull, ``VbmLlm.OpenAI.optNum_orNull]),
  O "openai-request-what-decodes-is-written-back-the-same" ["openai-chat:CreateChatCompletionRequest.messages"] (.proved [``VbmLlm.OpenAI.decode_ok_stable, ``VbmLlm.OpenAI.decodeMessages_ne_nil, ``VbmLlm.OpenAI.decodeEach_cons_ne_nil]),
  O "openai-request-decode-fails-closed" ["openai-chat:CreateChatCompletionRequest.messages", "openai-chat:CreateChatCompletionRequest.tool_choice", "openai-chat:CreateChatCompletionRequest.stream"]
    (.proved [``VbmLlm.OpenAI.Request.decode_not_object, ``VbmLlm.OpenAI.decodeMessages_none, ``VbmLlm.OpenAI.decodeMessages_empty, ``VbmLlm.OpenAI.decodeMessages_not_array,
      ``VbmLlm.OpenAI.decodeReqMessage_unsupported_role, ``VbmLlm.OpenAI.decodeReqMessage_user_content, ``VbmLlm.OpenAI.decodeToolChoice_unsupported, ``VbmLlm.OpenAI.optBool_wrong]),
  O "openai-stream-merge-rules" ["openai-chat:CreateChatCompletionStreamResponse.id", "openai-chat:CreateChatCompletionStreamResponse.model", "openai-chat:CreateChatCompletionStreamResponse.usage",
      "openai-chat:CreateChatCompletionStreamResponse.choices.finish_reason", "openai-chat:ChatCompletionStreamResponseDelta.content", "openai-chat:ChatCompletionStreamResponseDelta.refusal",
      "openai-chat:ChatCompletionMessageToolCallChunk.id", "openai-chat:ChatCompletionMessageToolCallChunk.function.name", "openai-chat:ChatCompletionMessageToolCallChunk.function.arguments"]
    (.proved [``VbmLlm.OpenAI.mergeCall_arguments, ``VbmLlm.OpenAI.mergeCall_id_first, ``VbmLlm.OpenAI.mergeCall_name_first, ``VbmLlm.OpenAI.mergeCall_id_kept, ``VbmLlm.OpenAI.mergeCall_name_kept,
      ``VbmLlm.OpenAI.applyChoice_content, ``VbmLlm.OpenAI.applyChoice_refusal, ``VbmLlm.OpenAI.applyChoice_finish, ``VbmLlm.OpenAI.applyChunk_id, ``VbmLlm.OpenAI.applyChunk_model, ``VbmLlm.OpenAI.applyChunk_usage]),
  O "openai-stream-chunk-boundaries-do-not-matter" ["openai-chat:ChatCompletionStreamResponseDelta.content", "openai-chat:ChatCompletionMessageToolCallChunk.function.arguments"]
    (.proved [``VbmLlm.OpenAI.foldPieces_eq, ``VbmLlm.OpenAI.pieces_content, ``VbmLlm.OpenAI.foldArgs_arguments, ``VbmLlm.OpenAI.foldArgs_id, ``VbmLlm.OpenAI.foldArgs_name]),
  O "openai-stream-missing-index-is-refused-by-default" ["openai-chat:CreateChatCompletionStreamResponse.choices.index", "openai-chat:ChatCompletionMessageToolCallChunk.index"]
    (.proved [``VbmLlm.OpenAI.applyCalls_missing_index_refused, ``VbmLlm.OpenAI.applyCalls_missing_index_zero, ``VbmLlm.OpenAI.foldItems_missing_index]),
  O "openai-stream-no-sentinel-is-never-complete" ["openai-chat-sse:sentinel"]
    (.proved [``VbmLlm.OpenAI.foldWith_no_done, ``VbmLlm.OpenAI.foldItems_complete, ``VbmLlm.OpenAI.foldItems_nil]),
  O "openai-stream-nothing-follows-the-sentinel" ["openai-chat-sse:sentinel"] (.proved [``VbmLlm.OpenAI.foldItems_after_done]),
  O "openai-stream-error-chunk-stops-the-fold-with-the-partial-reply" ["openai-chat-sse:error-chunk"] (.proved [``VbmLlm.OpenAI.foldItems_error_chunk, ``VbmLlm.OpenAI.errorOf_null, ``VbmLlm.OpenAI.errorOf_string, ``VbmLlm.OpenAI.errorOf_present]),
  O "openai-stream-a-complete-reply-has-a-choice" ["openai-chat-sse:complete-has-identity"] (.proved [``VbmLlm.OpenAI.foldWith_complete_choices]),
  O "openai-stream-chunk-is-an-object" ["openai-chat:CreateChatCompletionStreamResponse.choices"] (.proved [``VbmLlm.OpenAI.decodeChunk_not_object]),
  O "openai-stream-delta-and-fragment-shapes" ["openai-chat:CreateChatCompletionStreamResponse.choices.delta", "openai-chat:ChatCompletionStreamResponseDelta.tool_calls", "openai-chat:ChatCompletionMessageToolCallChunk.type"]
    (.proved [``VbmLlm.OpenAI.decodeChunkChoice_delta_wrong, ``VbmLlm.OpenAI.decodeChunkChoice_no_delta, ``VbmLlm.OpenAI.decodeDelta_tool_calls_wrong, ``VbmLlm.OpenAI.decodeToolCallDelta_other_type_refused]),
  O "openai-stream-events" ["openai-chat-sse:sentinel", "openai-chat-sse:event-type"]
    (.proved [``VbmLlm.OpenAI.decodeItem_done, ``VbmLlm.OpenAI.decodeItem_empty, ``VbmLlm.OpenAI.decodeItem_event_type]),
  O "openai-stream-fold-equals-single-shot" ["openai-chat-sse:complete-has-identity"]
    (.partly [``VbmLlm.OpenAI.pieces_content, ``VbmLlm.OpenAI.foldArgs_arguments, ``VbmLlm.OpenAI.foldWith_complete_choices]
      "proved: text and arguments split at any chunk boundary fold to the same strings, and a complete reply always has a choice. Open: the whole equality `fold (stream r) = r` for every well-formed stream (interleaved choices and calls); the recorded streams with a single-shot twin (`vectors/openai-chat-stream/*.single.json`) check it on data, not by proof"),
  -- the tool-call turn machine
  O "turn-every-call-is-answered-exactly-once-in-order" ["openai-chat-turn:answer-each-call-once", "openai-chat-turn:window", "openai-chat:ChatCompletionRequestToolMessage.tool_call_id"]
    (.proved [``VbmLlm.OpenAI.render_paired, ``VbmLlm.OpenAI.flatMap_render_paired, ``VbmLlm.OpenAI.seg_render_paired, ``VbmLlm.pair_calls, ``VbmLlm.pairFrom_calls, ``VbmLlm.close_calls, ``VbmLlm.feed_sound]),
  O "turn-an-unanswered-call-gets-a-placeholder-and-an-orphan-is-text" ["openai-chat-turn:unanswered-placeholder", "openai-chat-turn:orphan-is-text"]
    (.proved [``VbmLlm.pair_unanswered, ``VbmLlm.pair_orphan, ``VbmLlm.pair_orphan_after_assistant, ``VbmLlm.OpenAI.render_unanswered, ``VbmLlm.OpenAI.render_orphan]),
  O "turn-a-result-answers-its-call-and-the-newest-wins" ["openai-chat-turn:newest-result-wins", "openai-chat-turn:window"] (.proved [``VbmLlm.pair_answered, ``VbmLlm.pair_newest_wins, ``VbmLlm.OpenAI.render_answered]),
  O "turn-text-is-never-dropped-or-reordered" ["openai-chat-turn:text-keeps-its-order"] (.proved [``VbmLlm.pair_texts, ``VbmLlm.pairFrom_texts, ``VbmLlm.close_texts]),
  O "turn-extending-by-a-reply-leaves-what-was-rendered-as-it-was" ["openai-chat-turn:prefix-stable"]
    (.proved [``VbmLlm.OpenAI.render_prefix_stable, ``VbmLlm.pair_prefix_stable, ``VbmLlm.pairFrom_append_assistant]),
  -- the Anthropic messages adapter: the reply (the request, the stream and the turn shape are open)
  O "anthropic-reply-decode-is-characterised" ["anthropic-messages:Message.id", "anthropic-messages:Message.model", "anthropic-messages:Message.content", "anthropic-messages:Message.stop_reason", "anthropic-messages:Message.stop_sequence", "anthropic-messages:Message.usage"]
    (.proved [``VbmLlm.Anthropic.decode_ok_iff, ``VbmLlm.Anthropic.decodeContent_ok_iff, ``VbmLlm.Anthropic.decodeBlocks_ok_iff, ``VbmLlm.Anthropic.decode_not_object, ``VbmLlm.Anthropic.decode_no_content, ``VbmLlm.Anthropic.decode_content_not_array]),
  O "anthropic-blocks-keep-their-input-and-keep-unmodelled-types-raw" ["anthropic-messages:TextBlock.text", "anthropic-messages:ToolUseBlock.id", "anthropic-messages:ToolUseBlock.name", "anthropic-messages:ToolUseBlock.input", "anthropic-messages:ContentBlock.other", "anthropic-messages:ThinkingBlock.thinking", "anthropic-messages:ThinkingBlock.signature", "anthropic-messages:RedactedThinkingBlock.data"]
    (.proved [``VbmLlm.Anthropic.decodeBlock_thinking, ``VbmLlm.Anthropic.decodeBlock_redacted, ``VbmLlm.Anthropic.decodeBlock_of_type, ``VbmLlm.Anthropic.decodeBlock_text, ``VbmLlm.Anthropic.decodeBlock_toolUse, ``VbmLlm.Anthropic.decodeBlock_toolUse_no_input, ``VbmLlm.Anthropic.decodeBlock_other, ``VbmLlm.Anthropic.decodeBlock_no_type]),
  O "usage-anthropic-input-excludes-the-cache" ["anthropic-messages:Usage.input_tokens", "anthropic-messages:Usage.output_tokens", "anthropic-messages:Usage.cache_read_input_tokens", "anthropic-messages:Usage.cache_creation_input_tokens"]
    (.proved [``VbmLlm.Anthropic.decodeUsage_ok_iff, ``VbmLlm.Anthropic.tokens_uncached, ``VbmLlm.Anthropic.tokens_read, ``VbmLlm.Anthropic.tokens_write, ``VbmLlm.Anthropic.tokens_output, ``VbmLlm.Anthropic.tokens_input, ``VbmLlm.Anthropic.tokens_empty]),
  O "anthropic-stop-reason-is-kept-as-text-and-classed-totally" ["anthropic-messages:Message.stop_reason"]
    (.proved [``VbmLlm.FinishClass.ofAnthropic_end_turn, ``VbmLlm.FinishClass.ofAnthropic_stop_sequence, ``VbmLlm.FinishClass.ofAnthropic_tool_use, ``VbmLlm.FinishClass.ofAnthropic_pause_turn, ``VbmLlm.FinishClass.ofAnthropic_refusal,
      ``VbmLlm.FinishClass.ofAnthropic_truncated_iff, ``VbmLlm.FinishClass.ofAnthropic_unknown]),
  -- the Anthropic messages request: the encoder
  O "anthropic-request-members-are-the-fields" ["anthropic-messages:MessageCreateParams.model", "anthropic-messages:MessageCreateParams.max_tokens", "anthropic-messages:MessageCreateParams.messages",
      "anthropic-messages:MessageCreateParams.system", "anthropic-messages:MessageCreateParams.tools", "anthropic-messages:MessageCreateParams.tool_choice", "anthropic-messages:MessageCreateParams.stream",
      "anthropic-messages:MessageCreateParams.temperature", "anthropic-messages:MessageCreateParams.top_p", "anthropic-messages:MessageCreateParams.top_k", "anthropic-messages:MessageCreateParams.stop_sequences"]
    (.proved [``VbmLlm.Anthropic.encode_get_model, ``VbmLlm.Anthropic.encode_get_max_tokens, ``VbmLlm.Anthropic.encode_get_messages, ``VbmLlm.Anthropic.encode_get_system, ``VbmLlm.Anthropic.encode_get_tools,
      ``VbmLlm.Anthropic.encode_get_tool_choice, ``VbmLlm.Anthropic.encode_get_stream, ``VbmLlm.Anthropic.encode_get_temperature, ``VbmLlm.Anthropic.encode_get_top_p, ``VbmLlm.Anthropic.encode_get_top_k,
      ``VbmLlm.Anthropic.encode_get_stop_sequences, ``VbmLlm.Anthropic.encode_object]),
  O "anthropic-request-an-absent-field-is-left-out-never-null" ["anthropic-messages:MessageCreateParams.system", "anthropic-messages:MessageCreateParams.tools", "anthropic-messages:MessageCreateParams.stop_sequences",
      "anthropic-messages:ToolResultBlockParam.content", "anthropic-messages:ToolResultBlockParam.is_error"]
    (.proved [``VbmLlm.Anthropic.encode_members_not_null, ``VbmLlm.Anthropic.encodeBlock_toolResult]),
  O "anthropic-request-max-tokens-is-required-and-a-plain-natural" ["anthropic-messages:MessageCreateParams.max_tokens"] (.proved [``VbmLlm.Anthropic.encode_max_tokens_natural]),
  O "anthropic-request-a-tool-call-is-written-with-its-input-as-an-object" ["anthropic-messages:ToolUseBlockParam.input", "anthropic-messages:ToolResultBlockParam.tool_use_id"] (.proved [``VbmLlm.Anthropic.encodeBlock_toolUse]),
  -- the Anthropic messages request: the decoder, and the round trip
  O "anthropic-request-codec-round-trip" ["anthropic-messages:MessageCreateParams.model", "anthropic-messages:MessageCreateParams.max_tokens", "anthropic-messages:MessageCreateParams.messages", "anthropic-messages:MessageCreateParams.system", "anthropic-messages:MessageCreateParams.tools", "anthropic-messages:MessageCreateParams.tool_choice", "anthropic-messages:MessageCreateParams.stream", "anthropic-messages:MessageCreateParams.temperature", "anthropic-messages:MessageCreateParams.top_p", "anthropic-messages:MessageCreateParams.top_k", "anthropic-messages:MessageCreateParams.stop_sequences",
      "anthropic-messages:MessageParam.role", "anthropic-messages:MessageParam.content", "anthropic-messages:ToolUseBlockParam.input", "anthropic-messages:ToolResultBlockParam.tool_use_id",
      "anthropic-messages:ToolResultBlockParam.content", "anthropic-messages:ToolResultBlockParam.is_error", "anthropic-messages:Tool.name", "anthropic-messages:Tool.description",
      "anthropic-messages:Tool.input_schema", "anthropic-messages:Tool.strict"]
    (.proved [``VbmLlm.Anthropic.decode_encode, ``VbmLlm.Anthropic.decodeReqBlock_encodeBlock, ``VbmLlm.Anthropic.decodeMsg_encodeMessage, ``VbmLlm.Anthropic.decodeToolDecl_encodeTool,
      ``VbmLlm.Anthropic.decodeMsgs_encode, ``VbmLlm.Anthropic.decodeToolDecls_encode, ``VbmLlm.Anthropic.decodeToolPick_encode, ``VbmLlm.Anthropic.decodeStops_encode,
      ``VbmLlm.Anthropic.optStr_orNull, ``VbmLlm.Anthropic.reqNat_natNumber]),
  O "anthropic-request-what-decodes-is-written-back-the-same" ["anthropic-messages:MessageCreateParams.messages"]
    (.proved [``VbmLlm.Anthropic.decode_ok_stable, ``VbmLlm.Anthropic.decodeMsgs_ne_nil]),
  O "anthropic-request-decode-fails-closed" ["anthropic-messages:MessageCreateParams.max_tokens", "anthropic-messages:MessageCreateParams.messages", "anthropic-messages:MessageCreateParams.tool_choice",
      "anthropic-messages:MessageParam.role", "anthropic-messages:MessageParam.content"]
    (.proved [``VbmLlm.Anthropic.decode_not_object, ``VbmLlm.Anthropic.reqNat_missing, ``VbmLlm.Anthropic.decodeMsgs_none, ``VbmLlm.Anthropic.decodeMsgs_empty, ``VbmLlm.Anthropic.decodeMsgs_not_array,
      ``VbmLlm.Anthropic.decodeMsg_unsupported_role, ``VbmLlm.Anthropic.decodeReqBlock_unsupported_type, ``VbmLlm.Anthropic.decodeToolPick_unsupported]),
  O "anthropic-messages-adapter" [] (.open_ "the named-event stream fold and the turn shape over `pair` (the reply decoder, usage, stop reasons and the request codec with its round trip have landed above)"),
  -- OpenRouter's variant of the chat profile
  O "openrouter-finish-reason-error-is-its-own-class" ["openrouter-chat:finish-reason-error"] (.proved [``VbmLlm.FinishClass.ofOpenRouter_error, ``VbmLlm.FinishClass.ofOpenRouter_other]),
  O "openrouter-error-code-is-a-word-or-a-natural-never-coerced" ["openrouter-chat:Error.code", "openrouter-chat:Error.message"]
    (.proved [``VbmLlm.OpenRouter.optCode_ok_iff, ``VbmLlm.OpenRouter.optCode_wrong, ``VbmLlm.OpenRouter.decodeApiError_ok_iff, ``VbmLlm.OpenRouter.decodeApiError_not_object, ``VbmLlm.OpenRouter.decodeApiError_no_error,
      ``VbmLlm.OpenRouter.decodeApiError_no_message]),
  O "openrouter-chat-variant" ["openrouter-chat:usage-frame-has-choices", "openrouter-chat:mid-stream-error"]
    (.partly [``VbmLlm.OpenAI.applyChunk_usage, ``VbmLlm.OpenAI.foldItems_error_chunk, ``VbmLlm.OpenAI.applyChoice_finish]
      "proved: a usage report is read from any frame (so from one that has choices), an error chunk stops the fold with the partial reply, and the last finish reason wins (a repeated one changes nothing). Open: one theorem about a whole OpenRouter-shaped stream (the repeated finish reason on the usage frame leaves the reply as it was); the recorded stream `o001`, with its single-shot twin, checks it on data. Comment lines are the event splitter's (`vbm-sse`), not this library's"),
  O "decode-allocation-budget" [] (.open_ "a decoded reply allocates no more than the code it replaces on a recorded reply (measured by the consumer's footprint gate; the budget is stated here when the first consumer measures it)"),
  O "openai-reading-is-faithful-to-the-published-schema" [] (.limit "the clause index (docs/clause-index.txt) is read from the pinned OpenAPI document (docs/schemas/openai-chat.md); that each clause is stated faithfully is checked by review, never by a machine"),
  O "provider-honours-the-schema" [] (.limit "that a server sends what its schema says, that tool arguments are valid JSON or fit the declared parameters, that `model` names what served the call: client behaviour, not the wire contract"),
  O "the-pinned-parser-is-the-rfc-8259-reference" [] (.limit "the parse of the bytes is vbm-json's `parseFast`, proved there equal to its RFC 8259 reference; this library pins its revision and hash (scripts/pinned-libs.lock) and does not re-prove it")]
