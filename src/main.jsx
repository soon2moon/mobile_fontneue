import React from 'react';
import ReactDOM from 'react-dom/client';
import App from './App';
import './index.css';

class ErrorBoundary extends React.Component {
  constructor(props) {
    super(props);
    this.state = { error: null };
  }

  static getDerivedStateFromError(error) {
    return { error };
  }

  componentDidCatch(error, info) {
    console.error('[APP_CRASH]', error, info);
  }

  render() {
    if (this.state.error) {
      const message = this.state.error?.message || String(this.state.error);
      return (
        <div style={{ minHeight: '100vh', padding: 16, fontFamily: 'ui-sans-serif, system-ui, sans-serif', background: '#f4f1ed', color: '#4a2622' }}>
          <h1 style={{ margin: 0, fontSize: 18, fontWeight: 700 }}>Mobile Vector Editor failed to render</h1>
          <p style={{ marginTop: 8, fontSize: 13 }}>A runtime error occurred. Check browser console for details.</p>
          <pre style={{ marginTop: 12, padding: 12, borderRadius: 8, background: '#fff', border: '1px solid #d4c8c5', overflowX: 'auto', fontSize: 12 }}>
            {message}
          </pre>
        </div>
      );
    }
    return this.props.children;
  }
}

const rootElement = document.getElementById('root');
if (!rootElement) {
  throw new Error('Missing root element: #root');
}

ReactDOM.createRoot(rootElement).render(
  <React.StrictMode>
    <ErrorBoundary>
      <App />
    </ErrorBoundary>
  </React.StrictMode>
);
