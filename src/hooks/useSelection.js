import { useState } from 'react';

// Selection state: selected path points (as {pathIndex, pointIndex} refs),
// selected image ids, selected text ids, selected frame ids, and the path
// id under direct node-edit.
export function useSelection() {
  const [selectedPoints, setSelectedPoints] = useState([]);
  const [selectedImageIds, setSelectedImageIds] = useState([]);
  const [selectedTextIds, setSelectedTextIds] = useState([]);
  const [selectedFrameIds, setSelectedFrameIds] = useState([]);
  const [activePathEditId, setActivePathEditId] = useState(null);

  return {
    selectedPoints, setSelectedPoints,
    selectedImageIds, setSelectedImageIds,
    selectedTextIds, setSelectedTextIds,
    selectedFrameIds, setSelectedFrameIds,
    activePathEditId, setActivePathEditId
  };
}
