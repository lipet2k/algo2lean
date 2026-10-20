import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import tailwindcss from "@tailwindcss/vite";

// The built editor is committed under editor/ with fixed filenames so the
// Python server's asset allowlist, the site builders, and the release checks
// keep working unchanged. Paths stay relative because the same files are served
// from the local root, versions/v<VERSION>/, and current/.
const PYTHON_EDITOR = "http://127.0.0.1:8765";

function stableHtml() {
  return {
    name: "algo2lean-stable-html",
    transformIndexHtml: {
      order: "post",
      handler(html) {
        return html
          .replace(/<script type="module"[^>]*\bsrc="\.\/app\.js"[^>]*><\/script>/, '<script type="module" src="app.js"></script>')
          .replace(/<link rel="stylesheet"[^>]*\bhref="\.\/styles\.css"[^>]*>/, '<link rel="stylesheet" href="styles.css">');
      },
    },
  };
}

function proxy() {
  // The Python server accepts only its own localhost Host and no foreign Origin.
  return {
    target: PYTHON_EDITOR,
    changeOrigin: true,
    configure(server) {
      server.on("proxyReq", (request) => { request.removeHeader("origin"); });
    },
  };
}

export default defineConfig({
  root: "frontend",
  base: "./",
  plugins: [react(), tailwindcss(), stableHtml()],
  build: {
    outDir: "../editor",
    emptyOutDir: false,
    minify: false,
    cssCodeSplit: false,
    sourcemap: false,
    modulePreload: { polyfill: false },
    rollupOptions: {
      output: {
        codeSplitting: false,
        entryFileNames: "app.js",
        chunkFileNames: "[name].js",
        assetFileNames: (asset) => (asset.names || [asset.name]).some((name) => name && name.endsWith(".css")) ? "styles.css" : "[name][extname]",
      },
    },
  },
  server: {
    proxy: { "/api": proxy(), "/CITATION.cff": proxy(), "/analysis_export.py": proxy() },
  },
});
