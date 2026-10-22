import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import "./styles.css";
import App from "./App.jsx";
import { EditorStore } from "./editor/store.js";

// The store starts before rendering so Strict Mode's double effects cannot
// duplicate the initial compilation or the global listeners.
const store = new EditorStore();
store.start();
createRoot(document.getElementById("root")).render(<StrictMode><App store={store} /></StrictMode>);
