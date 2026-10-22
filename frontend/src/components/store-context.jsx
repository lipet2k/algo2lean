import { createContext, useContext, useEffect, useRef, useSyncExternalStore } from "react";

const StoreContext = createContext(null);
const StateContext = createContext(null);

export function StoreProvider({ store, children }) {
  const state = useSyncExternalStore(
    (listener) => store.subscribe(listener),
    () => store.getState(),
    () => store.getState(),
  );
  return (
    <StoreContext.Provider value={store}>
      <StateContext.Provider value={state}>{children}</StateContext.Provider>
    </StoreContext.Provider>
  );
}

export function useStore() {
  return useContext(StoreContext);
}

export function useEditorState() {
  return useContext(StateContext);
}

// Register a DOM node with the store under a name, for the few actions that
// move focus or trigger a hidden file input.
export function useRegistered(name) {
  const store = useStore();
  const ref = useRef(null);
  useEffect(() => {
    const element = ref.current;
    store.attach(name, element);
    return () => store.detach(name, element);
  }, [store, name]);
  return ref;
}
