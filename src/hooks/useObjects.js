import { useState } from 'react';

// Document content state: vector paths, placed images, and the in-progress
// pen/pencil path (with its target-layer info).
export function useObjects() {
  const [paths, setPaths] = useState([]);
  const [images, setImages] = useState([]);
  const [currentPath, setCurrentPath] = useState([]);
  const [currentPathInfo, setCurrentPathInfo] = useState(null);

  return {
    paths, setPaths,
    images, setImages,
    currentPath, setCurrentPath,
    currentPathInfo, setCurrentPathInfo
  };
}
