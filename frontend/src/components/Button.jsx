import { forwardRef } from "react";
import { cx } from "./classes.js";

const BASE = "inline-flex justify-center items-center gap-1.5 border rounded-lg text-[13px] font-[550] leading-5 whitespace-nowrap";
const SIZES = {
  default: "min-h-[38px] px-3 py-2 max-phone:min-h-11",
  icon: "w-9 h-9 p-0 max-phone:w-11 max-phone:h-11",
};
const VARIANTS = {
  quiet: "text-white bg-navy-600 border-navy-600 hover:enabled:bg-navy-500 hover:enabled:border-navy-500 active:enabled:bg-navy-700 active:enabled:border-navy-700",
  primary: "text-white bg-navy-800 border-navy-800 hover:enabled:bg-navy-700 hover:enabled:border-navy-700 active:enabled:bg-navy-900 active:enabled:border-navy-900 pr-2.5",
  danger: "text-white bg-error border-error hover:enabled:bg-error/85 hover:enabled:border-error/85 active:enabled:bg-error active:enabled:border-error",
};

export function buttonClass(variant = "quiet", size = "default", className) {
  return cx(BASE, SIZES[size], VARIANTS[variant], className);
}

export const Button = forwardRef(function Button({ variant = "quiet", size = "default", className, type = "button", ...props }, ref) {
  return <button ref={ref} type={type} className={buttonClass(variant, size, className)} {...props} />;
});

export function ClipboardIcon() {
  return (
    <svg viewBox="0 0 16 16" aria-hidden="true" fill="none" stroke="currentColor" strokeWidth="1.5" strokeLinecap="round" strokeLinejoin="round">
      <rect x="5.5" y="4.5" width="8" height="9.5" rx="1.5" />
      <path d="M10.5 4.5V3.5A1.5 1.5 0 0 0 9 2H4A1.5 1.5 0 0 0 2.5 3.5v6A1.5 1.5 0 0 0 4 11h1.5" />
    </svg>
  );
}
