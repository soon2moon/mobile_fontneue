// --- LAYER HELPER ---
export const generateLayerId = () => `layer-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;

export const createLayer = (type, existingCount) => {
   let name = "Vector";
   if (type === 'image') name = "Image";
   else if (type === 'text') name = "Text";
   else if (type === 'rectangle') name = "Rectangle";
   else if (type === 'ellipse') name = "Ellipse";
   else if (type === 'polygon') name = "Polygon";
   else if (type === 'star') name = "Star";
   else if (type === 'line') name = "Line";

   return {
       id: generateLayerId(),
       name: `${name} ${existingCount + 1}`,
       visible: true,
       locked: false,
       itemType: type || 'vector'
   };
};
