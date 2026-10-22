// Values derived from editor state. Components call these instead of the store
// keeping duplicated display fields in sync.
import { safeFilename, leanPath } from "../lib/names.js";

export function dirty(state) {
  return state.source !== state.savedSource || state.filename !== state.savedFilename;
}

export function analysisDirty(state) {
  return state.analysis !== state.savedAnalysis || state.analysisFilename !== state.savedAnalysisFilename;
}

export function saveStateText(state) {
  // Provenance such as "Example" or "Opened file" is implied by the toolbar,
  // so the tag reports only unsaved edits or a completed download.
  if (dirty(state)) return "Unsaved file";
  return state.saveStateLabel === "Downloaded" ? "Downloaded" : "";
}

export function analysisSaveStateText(state) {
  if (analysisDirty(state)) return "Unsaved file";
  return state.analysisSaveStateLabel === "Downloaded" ? "Downloaded" : "";
}

export function paneFilenames(state) {
  const inProject = Boolean(state.project);
  return {
    // Stale output still shows its original file until compilation replaces it.
    source: inProject ? state.filename : safeFilename(state.filename, ".algo"),
    analysis: inProject ? state.analysisFilename : safeFilename(state.analysisFilename, ".lean"),
    lean: leanPath(state.lastResult?.module || state.generatedModule, inProject),
    points: leanPath(state.lastResult?.pointsModule || state.generatedPointsModule, inProject),
  };
}

export function currentExample(state) {
  return !state.project && state.examples.find((example) => !example.project_id && example.filename === state.filename) || null;
}

export function currentOutput(state) {
  const result = state.lastResult;
  return Boolean(result && result.available && result.revision === state.revision &&
    result.source === state.source && result.filename === state.filename);
}

export function outputEnabled(state) {
  return !state.busy && currentOutput(state);
}

export function viewControlVisible(state) {
  return Boolean(state.lastResult) && Object.keys(state.lastResult.views || {}).length >= 2;
}

export function checkButtonLabel(state) {
  if (state.hosted) return "Check locally";
  if (state.project) return state.busy && state.busyCheck ? "Checking project…" : "Check project";
  return state.busy && state.busyCheck ? "Checking both files…" : "Check both files";
}

// Definition checks do not certify the optional Mathlib probability companion.
export function generatedLeanState(state) {
  const result = state.lastResult;
  if (result?.available && result.view === "probability") {
    return result.probabilityChecked ? { text: "Lean checked", tone: "checked" }
      : { text: "Requires Mathlib check", tone: "generated" };
  }
  return state.leanState;
}
