import { useState } from 'react';

// Selection state: selected path points (as {pathIndex, pointIndex} refs),
// selected image ids, and the path id under direct node-edit.
export function useSelection() {
  const [selectedPoints, setSelectedPoints] = useState([]);
  const [selectedImageIds, setSelectedImageIds] = useState([]);
  const [activePathEditId, setActivePathEditId] = useState(null);

  return {
    selectedPoints, setSelectedPoints,
    selectedImageIds, setSelectedImageIds,
    activePathEditId, setActivePathEditId
  };
}
