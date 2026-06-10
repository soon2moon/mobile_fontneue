import {
  Square,
  Circle,
  Triangle,
  Star,
  Minus,
  Image as ImageIcon,
  Type,
  PenTool
} from 'lucide-react';

const LayerIcon = ({ type }) => {
    switch(type) {
        case 'rectangle': return <Square size={14} className="text-[#667085]" />;
        case 'ellipse': return <Circle size={14} className="text-[#667085]" />;
        case 'polygon': return <Triangle size={14} className="text-[#667085]" />;
        case 'star': return <Star size={14} className="text-[#667085]" />;
        case 'line': return <Minus size={14} className="text-[#667085]" />;
        case 'image': return <ImageIcon size={14} className="text-[#667085]" />;
        case 'text': return <Type size={14} className="text-[#667085]" />;
        case 'vector':
        default:
            return <PenTool size={14} className="text-[#667085]" />;
    }
};

export default LayerIcon;
