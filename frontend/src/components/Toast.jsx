import { cx } from "./classes.js";
import { useEditorState, useStore } from "./store-context.jsx";

// Brief confirmations such as "Citation copied": green for success, red for
// failure, both with white text. The live region is always
// present so assistive technology announces each message; the card shows only
// while a toast is set and can be dismissed early with a click.
export function Toast() {
  const store = useStore();
  const { toast } = useEditorState();
  return (
    <div id="toast-region" className="fixed top-5 right-5 z-30 flex justify-end max-w-[calc(100%-40px)] pointer-events-none max-phone:top-3 max-phone:right-3 max-phone:max-w-[calc(100%-24px)]" role="status" aria-live="polite" aria-atomic="true">
      {toast && (
        <button id="toast" type="button" title="Dismiss" onClick={() => store.dismissToast()}
          className={cx("pointer-events-auto max-w-full px-4 py-2.5 rounded-lg border shadow-panel text-[13px] font-[550] leading-5 text-white text-left [overflow-wrap:anywhere]",
            toast.tone === "error" ? "bg-error border-error" : "bg-success border-success")}>
          {toast.text}
        </button>
      )}
    </div>
  );
}
