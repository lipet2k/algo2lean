// Shared class fragments for controls that appear in several panels.
export const cx = (...parts) => parts.filter(Boolean).join(" ");

export const selectClass = "select-control min-h-10 min-w-0 max-w-full px-3 py-2 text-[13px] max-phone:min-h-11 max-phone:text-base";
export const fieldLabelClass = "text-muted text-[13px]";
export const subtleLabelClass = "text-muted text-xs max-desktop:hidden";
export const paneFilenameClass = "block mt-1 text-muted text-xs leading-normal [overflow-wrap:anywhere]";
export const paneHeadingClass = "min-h-[66px] flex justify-between items-center gap-3 px-[18px] py-3 border-b border-border bg-linear-to-b from-navy-50 to-paper max-desktop:p-3 max-phone:flex-col max-phone:items-stretch max-phone:gap-2.5 max-phone:px-3 max-phone:py-3";
export const paneTitleClass = "flex items-center gap-2.5 min-w-0 flex-wrap max-desktop:gap-[7px] max-phone:gap-1.5";
export const paneHeadingTextClass = "text-sm font-[650] text-ink max-phone:text-[13px]";
export const paneFooterClass = "min-h-[43px] px-[18px] py-2 border-t border-border flex justify-between items-center gap-3 text-[11px] text-muted bg-paper max-phone:px-3 max-phone:py-[9px] max-phone:gap-2";
export const feedbackPanelClass = "px-5 pt-[17px] pb-[19px] bg-paper border border-navy-100 rounded-xl shadow-panel mt-4 max-phone:px-[14px] max-phone:py-[15px] max-phone:rounded-lg";
export const detailsSummaryClass = "text-ink py-1.5 font-[550]";
export const fileMessageClass = (error) => cx("mt-2.5 text-xs", error ? "text-error" : "text-muted");
export const dotClass = (lean) => cx("w-[7px] h-[7px] rounded-full flex-none", lean ? "bg-navy-500" : "bg-navy-800");

export function stateTagClass(tone) {
  const color = tone === "generated" || tone === "checked" ? "text-navy-700 bg-navy-100"
    : tone === "stale" ? "text-warning bg-warning-soft"
    : tone === "error" ? "text-error bg-error-soft"
    : "text-muted bg-navy-50";
  return cx("text-[11px] px-[7px] py-[3px] rounded-md whitespace-nowrap max-phone:text-[10px] max-phone:px-[5px]", color);
}

export function statusToneClass(tone) {
  return tone === "success" ? "text-success" : tone === "error" ? "text-error" : "text-muted";
}

export function blurOnEscape(event) {
  if (event.key === "Escape") { event.preventDefault(); event.currentTarget.blur(); }
}
