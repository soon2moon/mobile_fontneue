import { createContext, useContext } from 'react';

// One context carrying the editor's state + actions bundle, assembled in
// App.jsx (the composition root). Children destructure what they need via
// useEditor() instead of threading ~100 props.
const EditorContext = createContext(null);

export function EditorProvider({ value, children }) {
  return <EditorContext.Provider value={value}>{children}</EditorContext.Provider>;
}

export function useEditor() {
  const ctx = useContext(EditorContext);
  if (!ctx) throw new Error('useEditor must be used inside <EditorProvider>');
  return ctx;
}
