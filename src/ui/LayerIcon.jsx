import {
  Square,
  Circle,
  Triangle,
  Star,
  Minus,
  Image as ImageIcon,
  Type,
  Frame,
  PenTool
} from 'lucide-react';

const LayerIcon = ({ type }) => {
    switch(type) {
        case 'rectangle': return <Square size={14} className="text-secondary" />;
        case 'ellipse': return <Circle size={14} className="text-secondary" />;
        case 'polygon': return <Triangle size={14} className="text-secondary" />;
        case 'star': return <Star size={14} className="text-secondary" />;
        case 'line': return <Minus size={14} className="text-secondary" />;
        case 'image': return <ImageIcon size={14} className="text-secondary" />;
        case 'text': return <Type size={14} className="text-secondary" />;
        case 'frame': return <Frame size={14} className="text-secondary" />;
        case 'vector':
        default:
            return <PenTool size={14} className="text-secondary" />;
    }
};

export default LayerIcon;
