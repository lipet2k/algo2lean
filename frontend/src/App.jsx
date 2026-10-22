import { usePublication } from "./hooks/usePublication.js";
import { About } from "./components/About.jsx";
import { AnalysisPane } from "./components/AnalysisPane.jsx";
import { DocumentToolbar } from "./components/DocumentToolbar.jsx";
import { DraftPicker } from "./components/DraftPicker.jsx";
import { FeedbackPanel } from "./components/FeedbackPanel.jsx";
import { Footer } from "./components/Footer.jsx";
import { GenerationTools } from "./components/GenerationTools.jsx";
import { Header } from "./components/Header.jsx";
import { NewFileForm } from "./components/NewFileForm.jsx";
import { ProjectToolbar } from "./components/ProjectToolbar.jsx";
import { Toast } from "./components/Toast.jsx";
import { Welcome } from "./components/Welcome.jsx";
import { Workbench } from "./components/Workbench.jsx";
import { StoreProvider, useEditorState, useStore } from "./components/store-context.jsx";

function Editor() {
  const store = useStore();
  const state = useEditorState();
  const publication = usePublication(store);
  return (
    <>
      <a className="fixed -top-[70px] left-4 z-20 px-4 py-3 bg-paper border-2 border-navy-500 rounded-lg focus:top-3" href="#source">Skip to source editor</a>
      <Header publication={publication} />
      <main className="max-w-[1840px] px-8 pt-6 pb-[14px] mx-auto wide:pt-8 max-desktop:p-5 max-phone:px-3 max-phone:pt-4 max-phone:pb-3">
        <Welcome hosted={state.hosted} />
        <DocumentToolbar />
        <NewFileForm />
        <ProjectToolbar />
        <DraftPicker />
        <Workbench />
        <FeedbackPanel />
        <GenerationTools />
        <AnalysisPane />
        <About publication={publication} hosted={state.hosted} store={store} />
        <Footer publication={publication} />
      </main>
      <Toast />
    </>
  );
}

export default function App({ store }) {
  return (
    <StoreProvider store={store}>
      <Editor />
    </StoreProvider>
  );
}
